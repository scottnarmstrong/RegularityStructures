/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.TwoModel.LayerSumNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.TwoModel.GrowthCommonW
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# Window layer setting for the difference model, near-pair `Γ`-bounds

The lift `f⊕ = (λ Q f₁, f₁ − f₂)` of a pair of modelled distributions to the difference model
satisfies the window layer setting `LayerSettingWNear`, for models whose `Γ`-bounds hold only for
near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

/-- `LayerSettingWNear` for the lift `f⊕ = (λ Q f₁, f₁ - f₂)` of a pair on the difference model. -/
theorem layerSettingW_modelSum_near (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) {γ η α C₁ C₂ Cd CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam T : ℝ}
    {f₁ f₂ : ParabolicSpace → ι → ℝ}
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T)
    (hdP : M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow)
    (hdG : M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow)
    (hfd : M₁.SingularDiffBoundOn M₂ timeZeroDist γ η Cd (timeSlab T) f₁ f₂) :
    LayerSettingWNear (modelSum (lam := lam) h₁ h₂) (liftSum P lam f₁ f₂) γ η α (max (lam * C₁) Cd)
      (piConstSum lam CPi₂ CdPi) (gamConstSum lam CGam₁ CGam₂ CdGam) T where
  hγ := S₁.hγ
  hPi := piBoundOn_modelSum_const h₁ h₂ hlam S₂.hPi hdP
  hCPi := (S₂.hCPi).trans (le_max_left _ _)
  hGam := gammaBoundOn_modelSum_const_near h₁ h₂ hlam S₁.hGam S₂.hGam hdG
  hgrowth := exists_growthModel_modelSum h₁ h₂ hlam S₁.hgrowth S₂.hgrowth
  hT := S₁.hT
  hdeg s hs := by
    rcases s with i | j
    · exact S₁.hdeg i.1 hs
    · exact S₁.hdeg j hs
  hfT z s hs := by
    rcases s with i | j
    · have hi : γ ≤ 𝒯.deg i.1 := hs
      change lam * restrictNP P (f₁ z) i = 0
      rw [restrictNP_apply, S₁.hfT z i.1 hi, mul_zero]
    · have hj : γ ≤ 𝒯.deg j := hs
      change f₁ z j - f₂ z j = 0
      rw [S₁.hfT z j hj, S₂.hfT z j hj, sub_zero]
  hf := singularBoundOn_liftSum h₁ h₂ hlam S₁.hf hfd
  hf0 z hz := by
    change pairVec P (lam • restrictNP P (f₁ z)) (f₁ z - f₂ z) = 0
    rw [S₁.hf0 z hz, S₂.hf0 z hz]
    funext s
    rcases s with i | j <;> simp [pairVec]
  hα z s hs := by
    rcases s with i | j
    · have h1 : f₁ z i.1 ≠ 0 := fun h0 => hs (by
        change lam * restrictNP P (f₁ z) i = 0
        rw [restrictNP_apply, h0, mul_zero])
      exact S₁.hα z i.1 h1
    · by_cases h1 : f₁ z j = 0
      · have h2 : f₂ z j ≠ 0 := fun h0 => hs (by
          change f₁ z j - f₂ z j = 0
          rw [h1, h0, sub_zero])
        exact S₂.hα z j h2
      · exact S₁.hα z j h1
  hαγ := S₁.hαγ
  hαη := S₁.hαη
  hCf := (mul_nonneg hlam.le S₁.hCf).trans (le_max_left _ _)

end TwoModel

end RegularityStructures

end
