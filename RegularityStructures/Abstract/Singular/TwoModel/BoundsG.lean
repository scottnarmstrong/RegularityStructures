/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.DiffGrowthG
public import RegularityStructures.Abstract.Singular.TwoModel.LayerSum
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.PolyGrowth.Reconstruction
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# The difference model `M⊕` is a `GrowthModel`

Weighted version of `piBoundOn_modelSum`, `gammaBoundOn_modelSum_const`: from
`M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG`, `M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG` and the
weighted difference bounds `PiDiffBoundGrowth`, `GammaDiffBoundGrowth` we get

`(modelSum h₁ h₂).GrowthModel γ (piConstSum λ CPi₂ CdPi) (gamConstSum λ CGam₁ CGam₂ CdGam) ρP ρG p qG`

(`piConstSum λ CPi₂ CdPi = max CPi₂ (λ⁻¹ CdPi)`,
`gamConstSum λ CGam₁ CGam₂ CdGam = max (max (max CGam₁ CGam₂) (λ⁻¹ CdGam)) 0`).
-/

public section

open Set

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {γ CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

private theorem abs_inv_mul_le_growth {lam d C C' w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w)
    (h : |d| ≤ C * w) (hC : lam⁻¹ * C ≤ C') : |lam⁻¹ * d| ≤ C' * w := by
  rw [abs_mul, abs_of_pos (inv_pos.2 hlam)]
  calc lam⁻¹ * |d| ≤ lam⁻¹ * (C * w) := mul_le_mul_of_nonneg_left h (inv_pos.2 hlam).le
    _ = (lam⁻¹ * C) * w := by ring
    _ ≤ C' * w := mul_le_mul_of_nonneg_right hC hw

/-- Weighted `Π`-bound of the difference model, constant `max CPi₂ (λ⁻¹ CdPi)`. -/
theorem piBoundGrowth_modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) (G₂ : M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG)
    (hd : M₁.PiDiffBoundGrowth M₂ γ CdPi ρP) :
    (modelSum (lam := lam) h₁ h₂).PiBoundGrowth γ (piConstSum lam CPi₂ CdPi) ρP := by
  intro s hs t ht x
  have hρ : 0 < ρP x := G₂.moderateP.pos x
  have hw : 0 ≤ ρP x * t ^ ((structSumU P).deg s / parabolicSemigroup.order) :=
    mul_nonneg hρ.le (Real.rpow_nonneg ht.1.le _)
  have e : ∀ C : ℝ, C * ρP x * t ^ ((structSumU P).deg s / parabolicSemigroup.order) =
      C * (ρP x * t ^ ((structSumU P).deg s / parabolicSemigroup.order)) := fun C => by ring
  rw [e]
  rcases s with j | j
  · have hj : 𝒯.deg j.1 < γ := hs
    rw [Model.regPi, show ((modelSum (lam := lam) h₁ h₂).pi x (Pi.single (Sum.inl j) 1) :
        ℝ → ParabolicSpace → ℝ) t x = lam⁻¹ * (M₁.regPi x (Pi.single j.1 1) t x -
          M₂.regPi x (Pi.single j.1 1) t x) from coe_piSum_single_inl x j t x]
    refine abs_inv_mul_le_growth hlam hw ?_ (le_max_right _ _)
    rw [← e]
    exact hd j.1 hj t ht x
  · have hj : 𝒯.deg j < γ := hs
    rw [Model.regPi, show ((modelSum (lam := lam) h₁ h₂).pi x (Pi.single (Sum.inr j) 1) :
        ℝ → ParabolicSpace → ℝ) t x = M₂.regPi x (Pi.single j 1) t x from
        coe_piSum_single_inr x j t x]
    exact (G₂.piBound j hj t ht x).trans ((e CPi₂).le.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hw))

/-- Weighted `Γ`-bound of the difference model, constant `gamConstSum λ CGam₁ CGam₂ CdGam`. -/
theorem gammaBoundGrowth_modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) (G₁ : M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG)
    (G₂ : M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG)
    (hd : M₁.GammaDiffBoundGrowth M₂ γ CdGam ρG qG) :
    (modelSum (lam := lam) h₁ h₂).GammaBoundGrowth γ (gamConstSum lam CGam₁ CGam₂ CdGam) ρG qG := by
  intro s r hs hr x y
  have hρ : 0 < ρG x := G₂.moderateG.pos x
  have hd0 : 0 ≤ parabolicSemigroup.scaleDist y x :=
    parabolicSemigroup.scaleDist_nonneg _ _
  have hw : 0 ≤ ρG x * (1 + parabolicSemigroup.scaleDist y x) ^ qG *
      parabolicSemigroup.scaleDist y x ^ ((structSumU P).deg s - (structSumU P).deg r) :=
    mul_nonneg (mul_nonneg hρ.le (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg hd0 _)
  have e : ∀ C : ℝ, C * ρG x * (1 + parabolicSemigroup.scaleDist y x) ^ qG *
      parabolicSemigroup.scaleDist y x ^ ((structSumU P).deg s - (structSumU P).deg r) =
      C * (ρG x * (1 + parabolicSemigroup.scaleDist y x) ^ qG *
      parabolicSemigroup.scaleDist y x ^ ((structSumU P).deg s - (structSumU P).deg r)) :=
    fun C => by ring
  rw [e, gammaMap_modelSum]
  rcases s with i | i <;> rcases r with j | j
  · have hi : 𝒯.deg i.1 < γ := hs
    have hj : 𝒯.deg j.1 < 𝒯.deg i.1 := hr
    rw [gammaSum_single_inl_inl]
    refine (?_ : _ ≤ CGam₁ * _).trans (mul_le_mul_of_nonneg_right (le_gamConstSum_left _ _ _ _) hw)
    rw [← e]
    exact G₁.gammaBound i.1 j.1 hi hj x y
  · have hi : 𝒯.deg i.1 < γ := hs
    have hj : 𝒯.deg j < 𝒯.deg i.1 := hr
    rw [gammaSum_single_inl_inr]
    refine abs_inv_mul_le_growth hlam hw ?_ (le_gamConstSum_diff _ _ _ _)
    rw [← e]
    exact hd i.1 j hi hj x y
  · rw [gammaSum_single_inr_inl, abs_zero]
    exact mul_nonneg (gamConstSum_nonneg _ _ _ _) hw
  · have hi : 𝒯.deg i < γ := hs
    have hj : 𝒯.deg j < 𝒯.deg i := hr
    rw [gammaSum_single_inr_inr]
    refine (?_ : _ ≤ CGam₂ * _).trans (mul_le_mul_of_nonneg_right (le_gamConstSum_right _ _ _ _) hw)
    rw [← e]
    exact G₂.gammaBound i j hi hj x y

/-- **`M⊕` is a `GrowthModel`** (weighted `modelSum` bounds). -/
theorem growthModel_modelSum (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) (G₁ : M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG)
    (G₂ : M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG)
    (hdP : M₁.PiDiffBoundGrowth M₂ γ CdPi ρP) (hdG : M₁.GammaDiffBoundGrowth M₂ γ CdGam ρG qG) :
    (modelSum (lam := lam) h₁ h₂).GrowthModel γ (piConstSum lam CPi₂ CdPi)
      (gamConstSum lam CGam₁ CGam₂ CdGam) ρP ρG p qG where
  pos := G₁.pos
  moderateP := G₁.moderateP
  moderateG := G₁.moderateG
  nonnegG := G₁.nonnegG
  piBound := piBoundGrowth_modelSum h₁ h₂ hlam G₂ hdP
  gammaBound := gammaBoundGrowth_modelSum h₁ h₂ hlam G₁ G₂ hdG
  piBound_nonneg := G₂.piBound_nonneg.trans (le_max_left _ _)

end TwoModel

end RegularityStructures

end
