/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Sector
public import RegularityStructures.Abstract.Model

/-!
# Model bounds of the difference model

From `M_i.PiBoundOn`, `M_i.GammaBoundOn` and the difference bounds `PiDiffBoundOn`,
`GammaDiffBoundOn` (all on a set `S`, in particular `S = univ`, and at any level `γ`, in
particular `γ + 2`) we get the bounds of `M⊕`:

* `piBoundOn_modelSum`: constant `max CPi₂ (λ⁻¹ CdPi)`;
* `gammaBoundOn_modelSum`: constant `max (max CGam₁ CGam₂) (λ⁻¹ CdGam)`, assuming this constant
  is nonnegative (needed for the vanishing block `Γ⊕ e_{inr} → inl`).
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

theorem piBoundOn_modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) {γ CPi₂ CdPi : ℝ} {S : Set ParabolicSpace}
    (hPi₂ : M₂.PiBoundOn γ CPi₂ S) (hd : M₁.PiDiffBoundOn M₂ γ CdPi S) :
    (modelSum (lam := lam) h₁ h₂).PiBoundOn γ (max CPi₂ (lam⁻¹ * CdPi)) S := by
  intro s hs t ht x hx
  have hw : 0 ≤ t ^ ((structSumU P).deg s / parabolicSemigroup.order) :=
    Real.rpow_nonneg ht.1.le _
  rcases s with j | j
  · have hj : 𝒯.deg j.1 < γ := hs
    rw [Model.regPi, show ((modelSum (lam := lam) h₁ h₂).pi x (Pi.single (Sum.inl j) 1) :
        ℝ → ParabolicSpace → ℝ) t x = lam⁻¹ * (M₁.regPi x (Pi.single j.1 1) t x -
          M₂.regPi x (Pi.single j.1 1) t x) from coe_piSum_single_inl x j t x]
    exact abs_inv_mul_le hlam hw (hd j.1 hj t ht x hx) (le_max_right _ _)
  · have hj : 𝒯.deg j < γ := hs
    rw [Model.regPi, show ((modelSum (lam := lam) h₁ h₂).pi x (Pi.single (Sum.inr j) 1) :
        ℝ → ParabolicSpace → ℝ) t x = M₂.regPi x (Pi.single j 1) t x from
        coe_piSum_single_inr x j t x]
    exact (hPi₂ j hj t ht x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)

theorem gammaSum_single_inl_inl (x y : ParabolicSpace) (i j : NonPoly P) :
    gammaSum P lam M₁ M₂ x y (Pi.single (Sum.inl i) 1) (Sum.inl j) =
      M₁.gammaMap x y (Pi.single i.1 1) j.1 := by
  rw [gammaSum_apply_inl, single_inl, leftPart_pairVec, extendNP_single]

theorem gammaSum_single_inl_inr (x y : ParabolicSpace) (i : NonPoly P) (j : ι) :
    gammaSum P lam M₁ M₂ x y (Pi.single (Sum.inl i) 1) (Sum.inr j) =
      lam⁻¹ * (M₁.gammaMap x y (Pi.single i.1 1) j - M₂.gammaMap x y (Pi.single i.1 1) j) := by
  rw [gammaSum_apply_inr, single_inl, leftPart_pairVec, rightPart_pairVec, extendNP_single,
    map_zero, Pi.zero_apply, add_zero]

theorem gammaSum_single_inr_inl (x y : ParabolicSpace) (i : ι) (j : NonPoly P) :
    gammaSum P lam M₁ M₂ x y (Pi.single (Sum.inr i) 1) (Sum.inl j) = 0 := by
  rw [gammaSum_apply_inl, single_inr, leftPart_pairVec, map_zero, map_zero, Pi.zero_apply]

theorem gammaSum_single_inr_inr (x y : ParabolicSpace) (i j : ι) :
    gammaSum P lam M₁ M₂ x y (Pi.single (Sum.inr i) 1) (Sum.inr j) =
      M₂.gammaMap x y (Pi.single i 1) j := by
  rw [gammaSum_apply_inr, single_inr, leftPart_pairVec, rightPart_pairVec, map_zero, map_zero]
  simp

end TwoModel

end RegularityStructures

end
