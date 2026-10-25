/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.MeasJG
public import RegularityStructures.Abstract.Singular.KGamma.PairingG
public import RegularityStructures.Abstract.Singular.Kernel.Shell
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model

/-!
# Measurability of `x ↦ ⟨Π_x f(x), D^k K_n(x − ·)⟩`, weighted models

Weighted (`_growth`) version, for a `Model.GrowthModel`.

For measurable `f` with values in `T_{<γ}`, expanding `f(x)` in the basis,
`⟨Π_x f(x), g_x⟩ = ∑_i f(x)_i ⟨Π_x e_i, g_x⟩` (`pairing_regPi_eq_sum_single_of_scaled_growth`, `g_x` the
shell derivative, a scaled test function at `x`), and each `x ↦ ⟨Π_x e_i, g_x⟩` is the `n`-th term
of `jCoeffP`, measurable by `measurable_derivShellPairing_regPi_single_growth`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ} {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

theorem measurable_pairing_regPi_apply_lineIter_growth (hJ : M.IsJointMeasurable)
    (hh : ShellProfile h N) (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {f : ParabolicSpace → ι → ℝ}
    (hfm : Measurable f) (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) (k : Fin 4 →₀ ℕ) (n : ℕ) :
    Measurable fun x => parabolicSemigroup.pairing (M.regPi x (f x))
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) := by
  obtain ⟨C, -, hC⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  have e : (fun x => parabolicSemigroup.pairing (M.regPi x (f x))
      (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))) = fun x =>
      ∑ i, f x i * derivShellPairing (fun t y => M.regPi x (Pi.single i 1) t y) h k x n :=
    funext fun x => M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg (hfT x) (hC n x)
  rw [e]
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases hi : 𝒯.deg i < γ
  · exact ((measurable_pi_apply i).comp hfm).mul
      (measurable_derivShellPairing_regPi_single_growth hJ hh G hi hdeg k n)
  · have h0 : (fun x => f x i * derivShellPairing (fun t y => M.regPi x (Pi.single i 1) t y)
        h k x n) = fun _ => 0 :=
      funext fun x => by rw [(mem_lowerSubspace).1 (hfT x) i (not_lt.1 hi), zero_mul]
    rw [h0]
    exact measurable_const

end Model

end RegularityStructures

end
