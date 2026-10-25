/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Group
public import RegularityStructures.Abstract.Model

/-!
# The regularity structure `𝒯⊕` and its polynomial sector

* `gammaUnit`: `Γ⊕_{xy}` as a unit of `End`, with inverse `Γ⊕_{yx}`;
* `gammaUnit_mem_groupSumU`: every `Γ⊕_{xy}` lies in the model-independent group `groupSumU P`
  of `structSumU P` (`RegularityStructures.Abstract.Singular.TwoModel.Group`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  (P : PolynomialSector 𝒯 N') (lam : ℝ) (M₁ M₂ : Model 𝒯 parabolicSemigroup)

/-- `Γ⊕_{xy}` as a unit of `End`, with inverse `Γ⊕_{yx}`. -/
def gammaUnit (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) (x y : ParabolicSpace) :
    LinearMap.GeneralLinearGroup ℝ (NonPoly P ⊕ ι → ℝ) where
  val := gammaSum P lam M₁ M₂ x y
  inv := gammaSum P lam M₁ M₂ y x
  val_inv := by
    rw [Module.End.mul_eq_comp, gammaSum_comp h₁ h₂, gammaSum_self]
    rfl
  inv_val := by
    rw [Module.End.mul_eq_comp, gammaSum_comp h₁ h₂, gammaSum_self]
    rfl

end TwoModel

end RegularityStructures

end

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

theorem gammaUnit_self (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x : ParabolicSpace) : gammaUnit P lam M₁ M₂ h₁ h₂ x x = 1 :=
  Units.ext (gammaSum_self x)

theorem gammaUnit_mul (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x y z : ParabolicSpace) :
    gammaUnit P lam M₁ M₂ h₁ h₂ x y * gammaUnit P lam M₁ M₂ h₁ h₂ y z =
      gammaUnit P lam M₁ M₂ h₁ h₂ x z :=
  Units.ext (by
    rw [Units.val_mul, Module.End.mul_eq_comp]
    exact gammaSum_comp h₁ h₂ x y z)

theorem gammaUnit_mem_groupSumU (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (x y : ParabolicSpace) :
    gammaUnit P lam M₁ M₂ h₁ h₂ x y ∈ groupSumU P :=
  Subgroup.subset_closure ⟨_, (M₁.gamma x y).2, _, (M₂.gamma x y).2,
    fun _ hp => gammaMap_eq_of_mem_subspace h₁ h₂ x y hp, lam⁻¹, rfl⟩

end TwoModel

end RegularityStructures

end
