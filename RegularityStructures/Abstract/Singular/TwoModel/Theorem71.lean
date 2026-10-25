/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Realising
public import RegularityStructures.Abstract.Singular.TwoModel.LayerSum

/-!
# Hairer's Theorem 7.1, two-model (local Lipschitz) half

`Model.exists_singularDiffBoundOn_kGammaRem`: applying the single-model
`Model.exists_singularBoundOn_kGammaRem` to the difference model `M⊕` (structure `structSumU P`,
sector `V⊕`, integration `I⊕`, lift `f⊕`) gives, for the causal operator `kGammaRem`, the bound
`|||𝒦¹f₁ + R¹f₁ ; 𝒦²f₂ + R²f₂|||_{γ+2, α∧η+2; slab} ≤ C K⊕(λ) max (λ C₁, C_d)`
for every `λ > 0`, with `C` independent of the models, of `f₁, f₂`, of `T` and of `λ`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

/-- The constant `K⊕(λ)` of the two-model bound: `K₁` of the single-model theorem for the
difference model, with `n = |ι⊕|`. -/
def thm71SumConst (lam CPi₂ CdPi CGam₁ CGam₂ CdGam CΓ2₁ CΓ2₂ CdGam2 CI : ℝ) (n : ℕ) : ℝ :=
  (max 1 (gamConstSum lam CGam₁ CGam₂ CdGam) * piConstSum lam CPi₂ CdPi + n * CI) *
    max 1 (gamConstSum lam CΓ2₁ CΓ2₂ CdGam2)

end TwoModel

end RegularityStructures

end

