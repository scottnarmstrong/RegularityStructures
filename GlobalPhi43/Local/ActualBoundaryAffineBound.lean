/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.BoundaryKernelAgreement
public import GlobalPhi43.Local.AffineErrorComparison

/-! The quantitative boundary-potential bound for the ACTUAL ordinary
heat kernel, with one cutoff and constant before all source data. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric Filter Topology MeasureTheory
open scoped ContDiff ENNReal

 theorem small_pastBall_norm_le {y : ParabolicSpace} {R : ℝ}
    (hR : 0 ≤ R) (hRsmall : R ≤ 1 / 4) (hy : y ∈ pastBall 0 R) : ‖y‖ ≤ 1 / 4 := by
  have htime : |y.1| < R ^ 2 := by
    have hh := (Real.sqrt_lt (abs_nonneg ((0 : ℝ) - y.1)) hR).mp
      ((le_max_left _ _).trans_lt hy.1)
    simpa only [zero_sub, abs_neg] using hh
  have hspace : ‖y.2‖ < R := by
    have hh := (le_max_right _ _).trans_lt hy.1
    change ‖((0 : Fin 3 → ℝ) - y.2)‖ < R at hh
    simpa only [zero_sub, norm_neg] using hh
  rw [Prod.norm_def, Real.norm_eq_abs]
  apply max_le <;> nlinarith

/-- The compact extension disappears from the statement: this is the
actual heatKernelR4 boundary operator on the small past core. -/
theorem exists_actual_boundary_affine_bound : ∃ (χ : ParabolicSpace → ℝ) (C : ℝ),
    ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ range χ ⊆ Icc 0 1 ∧
    tsupport χ ⊆ closedBall 0 (3 / 4 : ℝ) ∧
    (∀ p ∈ closedBall 0 (1 / 2 : ℝ), χ p = 1) ∧ C > 0 ∧
    ∀ (μ : Measure ParabolicSpace), IsFiniteMeasure μ →
      ∀ (g : ParabolicSpace → ℝ) (H : ℝ), AEStronglyMeasurable g μ → 0 ≤ H →
      (∀ᵐ q ∂μ, |g q| ≤ H) → ∀ R : ℝ, 0 ≤ R → R ≤ 1 / 4 →
      pastAffineError (heatBoundaryPotential heatKernelR4 χ μ g) 0 R ≤
        ENNReal.ofReal (C * H * μ.real univ * R ^ 2) := by
  obtain ⟨χ, k, C, hχ, hcχ, hrange, hs, hone, _, _, he, hC, hbound⟩ :=
    exists_fixed_heat_boundary_affine_bound
  refine ⟨χ, C, hχ, hcχ, hrange, hs, hone, hC, ?_⟩
  intro μ hμ g H hg hH hgb R hR hRsmall
  have hclose : ∀ y ∈ pastBall (0 : ParabolicSpace) R,
      |heatBoundaryPotential heatKernelR4 χ μ g y - heatBoundaryPotential k χ μ g y| ≤ 0 := by
    intro y hy
    rw [heatBoundaryPotential_agreement hs hone he μ g (small_pastBall_norm_le hR hRsmall hy)]
    simp
  have herr := pastAffineError_le_of_close (heatBoundaryPotential heatKernelR4 χ μ g)
    (heatBoundaryPotential k χ μ g) 0 hclose
  have herr' : pastAffineError (heatBoundaryPotential heatKernelR4 χ μ g) 0 R ≤
      pastAffineError (heatBoundaryPotential k χ μ g) 0 R := by
    simpa only [ENNReal.ofReal_zero, add_zero] using herr
  exact herr'.trans (hbound μ hμ g H hg hH hgb 0 R hR)

end GlobalPhi43.Local
