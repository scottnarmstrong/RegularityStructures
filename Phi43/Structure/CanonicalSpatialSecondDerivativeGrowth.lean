/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSecondSpatialGrowth
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Linarith

/-!
# Spatial derivative growth of the smooth noise

This is the source-premise part of the higher-order Taylor estimate needed for
the global Gamma bound.  It turns the second iterated derivative bound on the
noise into a polynomial envelope for each fixed spatial directional derivative.
It introduces no model-bound hypothesis.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped ContDiff

theorem canonicalNoise_spatialDerivative_fderiv_growth
    (noise : CanonicalNoise) (C : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ q)
    (i : Fin 3) :
    PolyBounded (fun z => ‖fderiv ℝ
      (phi43SpatialDerivative noise.zeta i) z‖) := by
  let v : ParabolicSpace := phi43SpatialVector i
  have hf : ContDiff ℝ ∞ noise.zeta := noise.smooth
  have hsp : ContDiff ℝ ∞ (phi43SpatialDerivative noise.zeta i) := by
    unfold phi43SpatialDerivative
    have hc : ContDiff ℝ ∞ (fun z : ParabolicSpace => (z, v)) :=
      contDiff_id.prodMk contDiff_const
    simpa [Function.comp_def, v] using
      (hf.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (by simp)).comp hc
  have hC : 0 ≤ C := by
    have h0 := hg 0 (by omega) (0 : ParabolicSpace)
    simpa only [norm_iteratedFDeriv_zero, parabolicNorm_zero, add_zero,
      one_pow, mul_one] using (norm_nonneg (iteratedFDeriv ℝ 0 noise.zeta 0)).trans h0
  refine ⟨(hsp.continuous_fderiv (by simp)).norm.measurable,
    C * ‖v‖, q, ?_⟩
  intro z
  have hfd : DifferentiableAt ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z :=
    (hf.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiable (by simp) z
  have hconst : DifferentiableAt ℝ (fun _ : ParabolicSpace => v) z :=
    differentiableAt_const v
  have hmain :
      ‖fderiv ℝ (fun z : ParabolicSpace => (fderiv ℝ noise.zeta z) v) z‖ ≤
        (C * ‖v‖) * (1 + parabolicNorm z) ^ q := by
    rw [fderiv_clm_apply hfd hconst]
    have hzero : fderiv ℝ (fun _ : ParabolicSpace => v) z = 0 := by
      simp
    rw [hzero]
    simp only [ContinuousLinearMap.comp_zero, zero_add]
    have hflip :
        ‖(fderiv ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z).flip v‖ ≤
          ‖fderiv ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z‖ * ‖v‖ := by
      apply ContinuousLinearMap.opNorm_le_bound
      · positivity
      intro w
      rw [ContinuousLinearMap.flip_apply]
      calc
        ‖(fderiv ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z w) v‖ ≤
            ‖fderiv ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z w‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖fderiv ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z‖ * ‖w‖) *
            ‖v‖ := by
          exact mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ = (‖fderiv ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z‖ *
            ‖v‖) * ‖w‖ := by ring
    have htwo :
        ‖fderiv ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z‖ =
          ‖iteratedFDeriv ℝ 2 noise.zeta z‖ := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    calc
      _ ≤ ‖fderiv ℝ (fun z : ParabolicSpace => fderiv ℝ noise.zeta z) z‖ * ‖v‖ := hflip
      _ = ‖iteratedFDeriv ℝ 2 noise.zeta z‖ * ‖v‖ := by rw [htwo]
      _ ≤ (C * (1 + parabolicNorm z) ^ q) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (hg 2 (by omega) z) (norm_nonneg _)
      _ = (C * ‖v‖) * (1 + parabolicNorm z) ^ q := by ring
  change |‖fderiv ℝ (fun z : ParabolicSpace => (fderiv ℝ noise.zeta z) v) z‖| ≤ _
  simpa only [abs_of_nonneg (norm_nonneg _)] using hmain

end RegularityStructures.Phi43

end
