/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.OriginalDataBound

/-! Deterministic bounds for the original-data defect on a half-cylinder. -/
public noncomputable section
namespace GlobalPhi43
open RegularityStructures Set
open scoped ENNReal NNReal ContDiff

theorem mw20DefectBound :
    ∀ (Φ : ParabolicSpace → ℝ), IsMWTestKernel Φ →
    ∀ κ ∈ Ioo (0 : ℝ) (1 / 14), ∃ C : ℝ≥0,
    ∀ (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ),
      IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂ →
      ∀ R ∈ Ioo (0 : ℝ) 1,
        supNormOn (mwInnerCylinder R) (u - J) ≤ (C : ℝ≥0∞) *
          (max (ENNReal.ofReal (1 / R))
          (max (mwNegSeminorm Φ (-(1 / 2) - κ) (parabolicClosedNbhd mwCylinder 1) J ^ (1 / (1 * (1 / 2 - κ))))
          (max (mwNegSeminorm Φ (-1 - 2 * κ) (parabolicClosedNbhd mwCylinder 1) (fun z => J z ^ 2 - C₁) ^ (1 / (2 * (1 / 2 - κ))))
          (max (mwRecenteredSeminorm Φ (-(2 * κ)) (parabolicClosedNbhd mwCylinder 1) (fun x y => (J y ^ 2 - C₁) • (y.2 - x.2)) ^ (1 / (2 * (1 / 2 - κ))))
          (max (parabolicHolderSeminorm (1 - 2 * κ) (parabolicClosedNbhd mwCylinder 1) Y ^ (1 / (2 * (1 / 2 - κ))))
          (max (mwNegSeminorm Φ (-(3 / 2) - 3 * κ) (parabolicClosedNbhd mwCylinder 1) (fun z => J z ^ 3 - 3 * C₁ * J z) ^ (1 / (3 * (1 / 2 - κ))))
          (max (parabolicHolderSeminorm (1 / 2 - 3 * κ) (parabolicClosedNbhd mwCylinder 1) Z ^ (1 / (3 * (1 / 2 - κ))))
          (max (mwRecenteredSeminorm Φ (-(4 * κ)) (parabolicClosedNbhd mwCylinder 1) (fun x y => Y y * (J y ^ 2 - C₁) - C₂ - Y x * (J y ^ 2 - C₁)) ^ (1 / (4 * (1 / 2 - κ))))
          (max (mwRecenteredSeminorm Φ (-(4 * κ)) (parabolicClosedNbhd mwCylinder 1) (fun x y => Z y * J y - Z x * J y) ^ (1 / (4 * (1 / 2 - κ))))
          (max (mwRecenteredSeminorm Φ (-(1 / 2) - 5 * κ) (parabolicClosedNbhd mwCylinder 1) (fun x y => Z y * (J y ^ 2 - C₁) - 3 * C₂ * J y - Z x * (J y ^ 2 - C₁)) ^ (1 / (5 * (1 / 2 - κ))))
          (max (supNormOn (parabolicClosedNbhd mwCylinder 1) e₁ ^ (1 / 3 : ℝ))
          (max (supNormOn (parabolicClosedNbhd mwCylinder 1) e₂ ^ (1 / 2 : ℝ))
          (supNormOn (parabolicClosedNbhd mwCylinder 1) e₃ ^ (1 / 3 : ℝ)))))))))))))) :=
by
  intro Φ hΦ κ hκ
  obtain ⟨C, hC⟩ := Local.exists_original_data_bound hκ
  refine ⟨C, ?_⟩
  intro u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hd R hR
  exact hC Φ (Local.kernelProfile_of_isMWTestKernel hΦ) u ζ J Y Z e₁ e₂ e₃ C₁ C₂ hd R hR

end GlobalPhi43
