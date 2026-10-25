/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductDefs
public import RegularityStructures.Abstract.Singular.Slab.OperatorSlab

/-!
# Basis criteria for regular pairs and closure of coordinate sectors under the product

[Hai14, Definition 4.6]. For coordinate-closed sectors, the regularity of a pair `(V, W)` and the
inclusion `V ⋆ V ⊆ W` may be checked on basis vectors.
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace RegularityStructure

theorem GradedProduct.mul_sum_smul_sum (P : 𝒯.GradedProduct) (c d : ι → ℝ) (x y : ι → ι → ℝ) :
    P.mul (∑ τ, c τ • x τ) (∑ σ, d σ • y σ) =
      ∑ τ, ∑ σ, (c τ * d σ) • P.mul (x τ) (y σ) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem GradedProduct.mul_eq_sum_single (P : 𝒯.GradedProduct) (a b : ι → ℝ) :
    P.mul a b = ∑ τ, ∑ σ, (a τ * b σ) • P.mul (Pi.single τ 1) (Pi.single σ 1) := by
  conv_lhs => rw [eq_sum_single a, eq_sum_single b]
  exact P.mul_sum_smul_sum _ _ _ _

/-- A pair of coordinate-closed sectors is `γ`-regular as soon as the multiplicativity of the
group holds on the basis vectors of total degree `< γ`. -/
theorem GradedProduct.isRegularPair_of_single (P : 𝒯.GradedProduct)
    {V W : Submodule ℝ (ι → ℝ)} {γ : ℝ} (hV : IsCoordClosed V) (hW : IsCoordClosed W)
    (h : ∀ g ∈ 𝒯.group, ∀ τ σ : ι, (Pi.single τ 1 : ι → ℝ) ∈ V → (Pi.single σ 1 : ι → ℝ) ∈ W →
      𝒯.deg τ + 𝒯.deg σ < γ →
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
          (P.mul (Pi.single τ 1) (Pi.single σ 1)) =
        P.mul (((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
            (Pi.single τ 1))
          (((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
            (Pi.single σ 1))) :
    P.IsRegularPair V W γ := by
  intro g hg α β hαβ a ha haα b hb hbβ
  set L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) with hL
  have hLa : L a = ∑ τ, a τ • L (Pi.single τ 1) := by
    conv_lhs => rw [eq_sum_single a]
    simp only [map_sum, map_smul]
  have hLb : L b = ∑ σ, b σ • L (Pi.single σ 1) := by
    conv_lhs => rw [eq_sum_single b]
    simp only [map_sum, map_smul]
  rw [hLa, hLb, P.mul_sum_smul_sum, P.mul_eq_sum_single, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul]
  by_cases hτ : a τ = 0
  · simp [hτ]
  by_cases hσ : b σ = 0
  · simp [hσ]
  have hdτ : 𝒯.deg τ = α := not_not.1 fun h => hτ (haα τ h)
  have hdσ : 𝒯.deg σ = β := not_not.1 fun h => hσ (hbβ σ h)
  rw [h g hg τ σ (hV a ha τ hτ) (hW b hb σ hσ) (by rw [hdτ, hdσ]; exact hαβ)]

/-- `V ⋆ V ⊆ W` may be checked on the basis vectors of coordinate-closed `V`. -/
theorem GradedProduct.mul_mem_of_single (P : 𝒯.GradedProduct)
    {V W : Submodule ℝ (ι → ℝ)} (hV : IsCoordClosed V)
    (h : ∀ τ σ : ι, (Pi.single τ 1 : ι → ℝ) ∈ V → (Pi.single σ 1 : ι → ℝ) ∈ V →
      P.mul (Pi.single τ 1) (Pi.single σ 1) ∈ W) :
    ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W := by
  intro a ha b hb
  rw [P.mul_eq_sum_single]
  refine Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun σ _ => ?_
  by_cases hτ : a τ = 0
  · simp [hτ]
  by_cases hσ : b σ = 0
  · simp [hσ]
  exact Submodule.smul_mem _ _ (h τ σ (hV a ha τ hτ) (hV b hb σ hσ))

end RegularityStructure

end RegularityStructures

end
