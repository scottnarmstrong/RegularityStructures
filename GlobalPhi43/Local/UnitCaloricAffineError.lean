/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitCaloricAffineAllowance
public import GlobalPhi43.Local.ParabolicAffineError

/-! The unit caloric bound uses the actual affine error. Its finiteness is
proved from local smoothness on the closed past carrier. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric
open scoped ContDiff ENNReal

 theorem unit_pastAffineError_ne_top (h : ParabolicSpace → ℝ)
    (O : Set ParabolicSpace) (hKO : unitHeatPastCarrier ⊆ O)
    (hh : ContinuousOn h O) : pastAffineError h 0 1 ≠ ⊤ := by
  obtain ⟨B, hB⟩ := unitHeatPastCarrier_isCompact.exists_bound_of_continuousOn (hh.mono hKO)
  have hb : pastAffineError h 0 1 ≤ ENNReal.ofReal B := by
    apply pastAffineError_le_of_bound h 0 0 0
    intro y hy
    simpa [spatialAffine, spatialLinear, Real.norm_eq_abs] using
      hB y (unit_pastBall_subset_carrier hy)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

 theorem exists_unit_caloric_affine_error : ∃ C > 0,
    ∀ (h : ParabolicSpace → ℝ) (O : Set ParabolicSpace), IsOpen O →
      unitHeatPastCarrier ⊆ O → ContDiffOn ℝ ∞ h O →
      ∀ F : ℝ, 0 ≤ F →
      (∀ p ∈ pastBall (0 : ParabolicSpace) 1, |sourceHeat h p| ≤ F) →
      ∀ R : ℝ, 0 ≤ R → R ≤ 1 / 4 →
        pastAffineError h 0 R ≤
          ENNReal.ofReal (C * ((pastAffineError h 0 1).toReal * R ^ 2 + F)) := by
  obtain ⟨C, hC, hbound⟩ := exists_unit_caloric_affine_allowance
  refine ⟨C, hC, ?_⟩
  intro h O hO hKO hh F hF hPDE R hR hRsmall
  have hfin := unit_pastAffineError_ne_top h O hKO hh.continuousOn
  apply hbound h O hO hKO hh _ F ENNReal.toReal_nonneg hF _ hPDE R hR hRsmall
  exact (ENNReal.ofReal_toReal hfin).ge

end GlobalPhi43.Local
