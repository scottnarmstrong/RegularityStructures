/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.LayerSum
public import RegularityStructures.Abstract.Singular.TwoModel.BoundsNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.Singular.TwoModel.LayerSum`

The statements of `RegularityStructures.Abstract.Singular.TwoModel.LayerSum` that involve
`Γ`-bounds, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

end TwoModel

end RegularityStructures

end

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

theorem gammaBoundOn_modelSum_const_near (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) {γ CGam₁ CGam₂ CdGam : ℝ} {S : Set ParabolicSpace}
    (hG₁ : M₁.GammaNearOn γ CGam₁ S) (hG₂ : M₂.GammaNearOn γ CGam₂ S)
    (hd : M₁.GammaDiffNearOn M₂ γ CdGam S) :
    (modelSum (lam := lam) h₁ h₂).GammaNearOn γ (gamConstSum lam CGam₁ CGam₂ CdGam) S := by
  have hG₁' := Model.GammaNearOn.mono _ hG₁ (le_max_left CGam₁ 0)
  have h0 : 0 ≤ max (max (max CGam₁ 0) CGam₂) (lam⁻¹ * CdGam) :=
    (le_max_right CGam₁ 0).trans ((le_max_left (max CGam₁ 0) CGam₂).trans
      (le_max_left _ _))
  refine Model.GammaNearOn.mono _ (gammaBoundOn_modelSum_near h₁ h₂ hlam h0 hG₁' hG₂ hd) ?_
  exact max_le (max_le (max_le (le_gamConstSum_left _ _ _ _) (gamConstSum_nonneg _ _ _ _))
    (le_gamConstSum_right _ _ _ _)) (le_gamConstSum_diff _ _ _ _)

end TwoModel

end RegularityStructures

end
