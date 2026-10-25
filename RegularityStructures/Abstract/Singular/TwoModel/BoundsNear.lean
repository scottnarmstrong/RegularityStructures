/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Bounds
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.Singular.TwoModel.Bounds`

The statements of `RegularityStructures.Abstract.Singular.TwoModel.Bounds` that involve `Γ`-bounds,
for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

private theorem abs_inv_mul_le {lam d C C' w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w)
    (h : |d| ≤ C * w) (hC : lam⁻¹ * C ≤ C') : |lam⁻¹ * d| ≤ C' * w := by
  rw [abs_mul, abs_of_pos (inv_pos.2 hlam)]
  calc lam⁻¹ * |d| ≤ lam⁻¹ * (C * w) := mul_le_mul_of_nonneg_left h (inv_pos.2 hlam).le
    _ = (lam⁻¹ * C) * w := by ring
    _ ≤ C' * w := mul_le_mul_of_nonneg_right hC hw

theorem gammaBoundOn_modelSum_near (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) {γ CGam₁ CGam₂ CdGam : ℝ} {S : Set ParabolicSpace}
    (h0 : 0 ≤ max (max CGam₁ CGam₂) (lam⁻¹ * CdGam))
    (hG₁ : M₁.GammaNearOn γ CGam₁ S) (hG₂ : M₂.GammaNearOn γ CGam₂ S)
    (hd : M₁.GammaDiffNearOn M₂ γ CdGam S) :
    (modelSum (lam := lam) h₁ h₂).GammaNearOn γ (max (max CGam₁ CGam₂) (lam⁻¹ * CdGam)) S := by
  intro s r hs hr x hx y hy hxy
  have hw : 0 ≤ parabolicSemigroup.scaleDist y x ^
      ((structSumU P).deg s - (structSumU P).deg r) :=
    Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _
  rw [gammaMap_modelSum]
  rcases s with i | i <;> rcases r with j | j
  · have hi : 𝒯.deg i.1 < γ := hs
    have hj : 𝒯.deg j.1 < 𝒯.deg i.1 := hr
    rw [gammaSum_single_inl_inl]
    exact (hG₁ i.1 j.1 hi hj x hx y hy hxy).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) hw)
  · have hi : 𝒯.deg i.1 < γ := hs
    have hj : 𝒯.deg j < 𝒯.deg i.1 := hr
    rw [gammaSum_single_inl_inr]
    exact abs_inv_mul_le hlam hw (hd i.1 j hi hj x hx y hy hxy) (le_max_right _ _)
  · rw [gammaSum_single_inr_inl, abs_zero]
    exact mul_nonneg h0 hw
  · have hi : 𝒯.deg i < γ := hs
    have hj : 𝒯.deg j < 𝒯.deg i := hr
    rw [gammaSum_single_inr_inr]
    exact (hG₂ i j hi hj x hx y hy hxy).trans (mul_le_mul_of_nonneg_right
      ((le_max_right CGam₁ CGam₂).trans (le_max_left _ _)) hw)

end TwoModel

end RegularityStructures

end
