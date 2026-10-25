/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothRealisation
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel
import Mathlib.Tactic.FinCases

/-!
# Actual convolution and the constant Taylor-subtracted shell sum

Hairer [Hai14, (5.14), Definition 5.9, Proposition 8.27]. For target
homogeneity in `(0,1]`, only the constant Taylor term is subtracted.
The summed ordinary shell pairings equal the actual convolution minus
its value at the base point. No whole-space Q-tail or model-bound
hypotheses enter these local identities.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

local instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

local instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

private theorem taylorIdx_low {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    taylorIdx σ = {0} := by
  ext k
  rw [mem_taylorIdx_iff, Finset.mem_singleton]
  constructor
  · intro hk
    have hn : multiDeg k < 1 := by exact_mod_cast hk.trans_le hσ1
    have hz : multiDeg k = 0 := by omega
    unfold multiDeg at hz
    rw [weight_parabolicWeight] at hz
    ext i
    fin_cases i
    · change k (0 : Fin 4) = 0
      omega
    · change k (1 : Fin 4) = 0
      omega
    · change k (2 : Fin 4) = 0
      omega
    · change k (3 : Fin 4) = 0
      omega
  · rintro rfl
    simpa [multiDeg] using hσ0

private theorem taylorKernel_low (N n : ℕ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (x y w : ParabolicSpace) :
    taylorKernel (annKernel0C N) n σ x y w =
      annShellC N n (y - w) - annShellC N n (x - w) := by
  simp [taylorKernel, taylorIdx_low hσ0 hσ1, multiDirs, multiFact,
    evalParabolic, lineIter_nil, annShellC]

private theorem shell_reflect_integral (N n : ℕ) (f : ParabolicSpace → ℝ)
    (z : ParabolicSpace) :
    (∫ w, f w * annShellC N n (z - w)) = ∫ w, annShellC N n w * f (z - w) := by
  simpa only [sub_sub_cancel, mul_comm] using
    (integral_sub_left_eq_self (fun w => annShellC N n w * f (z - w)) volume z)

/-- The local constant-Taylor convolution identity, for every continuous input. -/
theorem hairerConvolution_eq_tsum_taylorKernel_low (N : ℕ)
    {f : ParabolicSpace → ℝ} (hf : Continuous f) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (x y : ParabolicSpace) :
    hairerConvolution N f y - hairerConvolution N f x =
      ∑' n : ℕ, ∫ w, f w * taylorKernel (annKernel0C N) n σ x y w := by
  have hint (n : ℕ) (z : ParabolicSpace) :
      Integrable (fun w => f w * annShellC N n (z - w)) :=
    (hf.mul ((contDiff_annShellC N n).continuous.comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        (((hasCompactSupport_scaledShell (fun _ hz => annKernel0C_eq_zero N hz) n).comp_homeomorph
          (Homeomorph.subLeft z)).mul_left)
  have hs (z : ParabolicSpace) :
      Summable (fun n : ℕ => ∫ w, f w * annShellC N n (z - w)) := by
    simp_rw [shell_reflect_integral]
    exact (canonicalShell_summable_integral_norm N hf z).of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  have hc (z : ParabolicSpace) : hairerConvolution N f z =
      ∑' n : ℕ, ∫ w, f w * annShellC N n (z - w) := by
    rw [hairerConvolution_eq_tsum_shellConvolution N hf z]
    exact tsum_congr (fun n => (shell_reflect_integral N n f z).symm)
  have he (n : ℕ) :
      (∫ w, f w * taylorKernel (annKernel0C N) n σ x y w) =
        (∫ w, f w * annShellC N n (y - w)) -
          (∫ w, f w * annShellC N n (x - w)) := by
    simp_rw [taylorKernel_low N n hσ0 hσ1, mul_sub]
    exact integral_sub (hint n y) (hint n x)
  rw [hc y, hc x, ← (hs y).tsum_sub (hs x)]
  exact tsum_congr (fun n => (he n).symm)

end RegularityStructures.Phi43

end
