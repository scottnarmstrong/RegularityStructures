/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Poly
public import RegularityStructures.Abstract.Model

/-!
# The difference-model transformations `Γ⊕`

`Γ⊕_{xy} (a, b) = (Q Γ¹_{xy} E₀ a, λ⁻¹ (Γ¹_{xy} - Γ²_{xy}) E₀ a + Γ²_{xy} b)` (`gammaSum`), a
block-triangular linear map of `ι⊕ → ℝ`. For polynomial-compatible `M₁, M₂`:

* `gammaSum_self`: `Γ⊕_{xx} = id`, `gammaSum_comp`: `Γ⊕_{xy} ∘ Γ⊕_{yz} = Γ⊕_{xz}`;
* `isGradedUnipotent_gammaSum`: graded unipotence for `degSum P`;
* `gammaUnit`: `Γ⊕_{xy}` as a unit of `End`, with inverse `Γ⊕_{yx}`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  (P : PolynomialSector 𝒯 N') (lam : ℝ) (M₁ M₂ : Model 𝒯 parabolicSemigroup)

/-- `Γ⊕_{xy} (a, b) = (Q Γ¹_{xy} E₀ a, λ⁻¹ (Γ¹_{xy} - Γ²_{xy}) E₀ a + Γ²_{xy} b)`. -/
def gammaSum (x y : ParabolicSpace) : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ) :=
  blockMap P (restrictNP P ∘ₗ M₁.gammaMap x y ∘ₗ extendNP P)
    (lam⁻¹ • ((M₁.gammaMap x y - M₂.gammaMap x y) ∘ₗ extendNP P)) (M₂.gammaMap x y)

end TwoModel

end RegularityStructures

end

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

theorem gammaSum_pairVec (x y : ParabolicSpace) (a : NonPoly P → ℝ) (b : ι → ℝ) :
    gammaSum P lam M₁ M₂ x y (pairVec P a b) =
      pairVec P (restrictNP P (M₁.gammaMap x y (extendNP P a)))
        (lam⁻¹ • (M₁.gammaMap x y (extendNP P a) - M₂.gammaMap x y (extendNP P a)) +
          M₂.gammaMap x y b) := rfl

theorem gammaSum_apply_inl (x y : ParabolicSpace) (v : NonPoly P ⊕ ι → ℝ) (i : NonPoly P) :
    gammaSum P lam M₁ M₂ x y v (Sum.inl i) =
      M₁.gammaMap x y (extendNP P (leftPart P v)) i.1 := rfl

theorem gammaSum_apply_inr (x y : ParabolicSpace) (v : NonPoly P ⊕ ι → ℝ) (j : ι) :
    gammaSum P lam M₁ M₂ x y v (Sum.inr j) =
      lam⁻¹ * (M₁.gammaMap x y (extendNP P (leftPart P v)) j -
        M₂.gammaMap x y (extendNP P (leftPart P v)) j) +
        M₂.gammaMap x y (rightPart P v) j := rfl

theorem gammaSum_self (x : ParabolicSpace) : gammaSum P lam M₁ M₂ x x = LinearMap.id := by
  have : gammaSum P lam M₁ M₂ x x = blockMap P LinearMap.id 0 LinearMap.id := by
    unfold gammaSum
    refine blockMap_ext P ?_ ?_ ?_
    · refine LinearMap.ext fun a => ?_
      simp [Model.gammaMap_self]
    · refine LinearMap.ext fun a => ?_
      simp [Model.gammaMap_self]
    · exact M₂.gammaMap_self x
  rw [this, blockMap_id]

theorem gammaSum_comp (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x y z : ParabolicSpace) :
    gammaSum P lam M₁ M₂ x y ∘ₗ gammaSum P lam M₁ M₂ y z = gammaSum P lam M₁ M₂ x z := by
  unfold gammaSum
  rw [blockMap_comp]
  refine blockMap_ext P ?_ ?_ ?_
  · refine LinearMap.ext fun a => ?_
    simp only [LinearMap.comp_apply]
    rw [restrictNP_gammaMap_extendNP_restrictNP, ← LinearMap.comp_apply (M₁.gammaMap x y),
      M₁.gammaMap_comp]
  · refine LinearMap.ext fun a => ?_
    have e1 : M₁.gammaMap x z (extendNP P a) = M₁.gammaMap x y (M₁.gammaMap y z (extendNP P a)) :=
      (LinearMap.congr_fun (M₁.gammaMap_comp x y z) _).symm
    have e2 : M₂.gammaMap x z (extendNP P a) = M₂.gammaMap x y (M₂.gammaMap y z (extendNP P a)) :=
      (LinearMap.congr_fun (M₂.gammaMap_comp x y z) _).symm
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, gammaMap_sub_extendNP_restrictNP h₁ h₂, map_sub, map_smul, e1, e2]
    module
  · exact M₂.gammaMap_comp x y z

end TwoModel

end RegularityStructures

end
