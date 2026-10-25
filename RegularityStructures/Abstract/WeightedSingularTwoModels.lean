/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularProduct
public import RegularityStructures.Abstract.ProductTwoModels
public import RegularityStructures.Abstract.Model

/-!
# Products of singular modelled distributions for two models

The second part of [Hai14, Proposition 6.12]: in the situation of Proposition 4.10, with
`f = f₁ ⋆_γ f₂` and `g = g₁ ⋆_γ g₂`,
`|||f; g|||_{γ,η} ≲ |||f₁; g₁|||_{γ₁,η₁} + |||f₂; g₂|||_{γ₂,η₂} + ‖Γ − Γ̄‖` uniformly over bounded
norms. We prove the explicit form (`Model.singularDiffBoundOn_truncMul`):
`|||f; g|||_{γ,η;S} ≤ c (δ₁ C₂ + C₁ δ₂ + 2 C₁ C₂ δ_Γ) (1 + C_Γ)²`, `c = (3 + |ι|⁴) ‖⋆‖`, with the
same conventions as `Model.modelledDiffBoundOn_truncMul`, under the hypothesis `η ≤ γ` (which is
necessary already for the first part, see `RegularityStructures.Abstract.WeightedSingularProduct`).

Source: [Hai14] = arXiv:1303.5113v4, Proposition 6.12 and its proof.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The sup part of `|||f; g|||_{γ,η}` evaluated with any weight `0 < w ≤ ‖x‖_P`. -/
theorem SingularDiffBoundOn.abs_sub_apply_le_weight {M₁ M₂ : Model 𝒯 K} {ρ : E → ℝ}
    {γ η δ : ℝ} {S : Set E} {f g : E → ι → ℝ} (hδ : M₁.SingularDiffBoundOn M₂ ρ γ η δ S f g)
    (hδ0 : 0 ≤ δ) {x : E} (hfT : f x ∈ lowerSubspace 𝒯.deg γ)
    (hgT : g x ∈ lowerSubspace 𝒯.deg γ) (hx : x ∈ S) (hρ : 0 < ρ x) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ singularWeight ρ x) (i : ι) : |f x i - g x i| ≤ δ * w ^ min (η - 𝒯.deg i) 0 := by
  by_cases hi : 𝒯.deg i < γ
  · refine (hδ.1 x hx hρ i hi).trans (mul_le_mul_of_nonneg_left ?_ hδ0)
    exact Real.rpow_le_rpow_of_nonpos hw0 hw (min_le_right _ _)
  · rw [hfT i (not_lt.1 hi), hgT i (not_lt.1 hi), sub_zero, abs_zero]
    exact mul_nonneg hδ0 (Real.rpow_nonneg hw0.le _)

end Model

end RegularityStructures

end
