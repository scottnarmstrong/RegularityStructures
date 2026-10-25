/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.JSumG
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Singular.Remainder.GammaG
public import RegularityStructures.Abstract.Model

/-!
# Identification of `𝒦⊕ f⊕` for a kernel pair, under weighted bounds

For a kernel pair `(h, r)` (`KernelPair h r N`, `N' ≤ N`), weighted layer settings
(`LayerSettingG`) of `(M₁, f₁)`, `(M₂, f₂)`, and the lift `f⊕ = liftSum P λ f₁ f₂` on the time slab:

* `kGammaRemG_modelSum_parts_growth`:
  `leftPart (M⊕.kGammaRemG h r P⊕ I⊕ γ f⊕ x) = λ • Q (I (f₁ x))` and
  `rightPart (M⊕.kGammaRemG h r P⊕ I⊕ γ f⊕ x) =
    M₁.kGammaRemG h r P I γ f₁ x - M₂.kGammaRemG h r P I γ f₂ x`;
* `rightPart_sub_gammaSum_kGammaRemG_growth`: the increment identity
  `rightPart (F⊕ y - Γ⊕_{yx} F⊕ x) = (F₁ y - Γ¹_{yx} F₁ x) - (F₂ y - Γ²_{yx} F₂ x)`.
-/

public section

namespace RegularityStructures

namespace TwoModel

open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {V : Submodule ℝ (ι → ℝ)} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {f₁ f₂ : ParabolicSpace → ι → ℝ} {γ η α C₁ C₂ CPi₁ CPi₂ CGam₁ CGam₂ T p qG Rw : ℝ}
  {ρP ρG : ParabolicSpace → ℝ} {h r : ParabolicSpace → ℝ} {N : ℕ}

theorem kGammaRemG_sub_mem_subspace (M : Model 𝒯 parabolicSemigroup) (h r : ParabolicSpace → ℝ)
    (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    M.kGammaRemG h r P I γ f x - I (f x) ∈ P.subspace := by
  have : M.kGammaRemG h r P I γ f x - I (f x) =
      jMapP M h P x (f x) + M.nVecS h P γ f x + M.remVecG r P γ f x := by
    unfold Model.kGammaRemG Model.kGammaS
    abel
  rw [this]
  exact P.subspace.add_mem (P.subspace.add_mem (jMapP_mem_subspace _ _ _ _ _)
    (Model.nVecS_mem_subspace _ _ _ _ _ _)) (Model.remVecG_mem_subspace _ _ _ _ _ _)

end TwoModel

end RegularityStructures

end
