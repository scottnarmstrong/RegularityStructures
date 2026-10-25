/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Bounds
public import RegularityStructures.Abstract.Singular.TwoModel.Lift
public import RegularityStructures.Abstract.Singular.Layer.Setting
public import RegularityStructures.Abstract.Model

/-!
# `LayerSetting` for the difference model

`layerSetting_modelSum`: from `LayerSetting M₁ f₁ …`, `LayerSetting M₂ f₂ …` (same `γ, η, α, T`),
the model-difference bounds `PiDiffBoundOn`, `GammaDiffBoundOn` and the comparison
`SingularDiffBoundOn` of `f₁, f₂`, the lift `f⊕ = liftSum P λ f₁ f₂` satisfies
`LayerSetting M⊕ f⊕ γ η α (max (λ C₁) Cd) (piConstSum λ CPi₂ CdPi)
  (gamConstSum λ CGam₁ CGam₂ CdGam) T`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

/-- The `Π`-constant `max CPi₂ (λ⁻¹ CdPi)` of the difference model. -/
def piConstSum (lam CPi₂ CdPi : ℝ) : ℝ := max CPi₂ (lam⁻¹ * CdPi)

/-- The `Γ`-constant `max (max CGam₁ CGam₂) (λ⁻¹ CdGam) ∨ 0` of the difference model. -/
def gamConstSum (lam CGam₁ CGam₂ CdGam : ℝ) : ℝ :=
  max (max (max CGam₁ CGam₂) (lam⁻¹ * CdGam)) 0

end TwoModel

end RegularityStructures

end

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

theorem le_gamConstSum_left (lam CGam₁ CGam₂ CdGam : ℝ) :
    CGam₁ ≤ gamConstSum lam CGam₁ CGam₂ CdGam :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem le_gamConstSum_right (lam CGam₁ CGam₂ CdGam : ℝ) :
    CGam₂ ≤ gamConstSum lam CGam₁ CGam₂ CdGam :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem le_gamConstSum_diff (lam CGam₁ CGam₂ CdGam : ℝ) :
    lam⁻¹ * CdGam ≤ gamConstSum lam CGam₁ CGam₂ CdGam :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem gamConstSum_nonneg (lam CGam₁ CGam₂ CdGam : ℝ) : 0 ≤ gamConstSum lam CGam₁ CGam₂ CdGam :=
  le_max_right _ _

theorem piBoundOn_modelSum_const (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : 0 < lam) {γ CPi₂ CdPi : ℝ} {S : Set ParabolicSpace}
    (hPi₂ : M₂.PiBoundOn γ CPi₂ S) (hd : M₁.PiDiffBoundOn M₂ γ CdPi S) :
    (modelSum (lam := lam) h₁ h₂).PiBoundOn γ (piConstSum lam CPi₂ CdPi) S :=
  piBoundOn_modelSum h₁ h₂ hlam hPi₂ hd

end TwoModel

end RegularityStructures

end
