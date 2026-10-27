/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitHeatSource
public import GlobalPhi43.Local.ActualBoundaryAffineBound

/-! The actual boundary estimate with the exact local unit-box field
allowance. The extension is qualitative; its norms never enter the bound. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric Filter Topology MeasureTheory
open scoped ContDiff ENNReal

 theorem exists_unit_boundary_affine_bound : ∃ (χ : ParabolicSpace → ℝ) (C : ℝ),
    ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ range χ ⊆ Icc 0 1 ∧
    tsupport χ ⊆ closedBall 0 (3 / 4 : ℝ) ∧
    (∀ p ∈ closedBall 0 (1 / 2 : ℝ), χ p = 1) ∧ C > 0 ∧
    ∀ (h : ParabolicSpace → ℝ) (O : Set ParabolicSpace), IsOpen O →
      unitHeatPastCarrier ⊆ O → ContDiffOn ℝ ∞ h O →
      ∀ H : ℝ, 0 ≤ H → (∀ p ∈ pastBall (0 : ParabolicSpace) 1, |h p| ≤ H) →
      ∃ g : ParabolicSpace → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        (∀ p ∈ unitHeatPastCarrier, g =ᶠ[𝓝 p] h) ∧
        ∀ R : ℝ, 0 ≤ R → R ≤ 1 / 4 →
          pastAffineError (heatBoundaryPotential heatKernelR4 χ unitHeatSourceMeasure g) 0 R ≤
            ENNReal.ofReal (C * H * R ^ 2) := by
  obtain ⟨χ, C, hχ, hcχ, hrange, hs, hone, hC, hbound⟩ := exists_actual_boundary_affine_bound
  have hm : 0 ≤ unitHeatSourceMeasure.real univ := ENNReal.toReal_nonneg
  have hnew : 0 < 1 + C * unitHeatSourceMeasure.real univ := by nlinarith
  refine ⟨χ, 1 + C * unitHeatSourceMeasure.real univ, hχ, hcχ, hrange, hs, hone, hnew, ?_⟩
  intro h O hO hKO hh H hH hHbound
  obtain ⟨g, hg, hcg, he⟩ := exists_compact_smooth_extension unitHeatPastCarrier_isCompact hO hKO hh
  refine ⟨g, hg, hcg, he, ?_⟩
  intro R hR hRsmall
  have hraw := hbound unitHeatSourceMeasure inferInstance g H hg.continuous.aestronglyMeasurable
    hH (unit_source_extension_bound he hHbound) R hR hRsmall
  apply hraw.trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [mul_nonneg hH (sq_nonneg R)]

end GlobalPhi43.Local
