/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularBounds
public import RegularityStructures.Abstract.Model

/-!
# Multiplication of singular modelled distributions

[Hai14, Proposition 6.12]: let `f₁ ∈ D^{γ₁,η₁}_P(V)`, `f₂ ∈ D^{γ₂,η₂}_P(W)` for sectors of
regularities `α₁`, `α₂`, and let `(V, W)` be `γ`-regular with `γ = (γ₁ + α₂) ∧ (γ₂ + α₁)`. Then
`f₁ ⋆_γ f₂ ∈ D^{γ,η}_P` with `η = (η₁ + α₂) ∧ (η₂ + α₁) ∧ (η₁ + η₂)`.

**An extra hypothesis is needed: `η ≤ γ`.** Without it the statement is false. Counterexample:
the polynomial structure on `ℝ` truncated at degree `1` (`T = ⟨1, X⟩`, `X ⋆ X = 0`), which is
`γ`-regular for `γ ≤ 2`, `P = {0}`, `γ₁ = γ₂ = γ ∈ (1, 2)`, `α₁ = α₂ = 0`, and
`f₁ = f₂ = φ 1 + φ' X` with `φ` smooth and bounded, `φ(x) = x` near `0`. Near `P` the
increments of `fᵢ` vanish, so `fᵢ ∈ D^{γ,η₁}_P` for every `η₁ ≥ 0`, e.g. `η₁ = η₂ = 3`, giving
`η = 3 > γ`. But the `X`-component of the increment of `f₁ ⋆_γ f₂ = φ² 1 + 2φφ' X` between
`x = λ` and `y = 2λ` is `2λ`, while `D^{γ,3}_P` requires `≲ λ^{γ−1} λ^{3−γ} = λ²`. In Hairer's
proof this is the case `m ≤ η₁`, `n ≤ η₂` of the bound (6.12), where the exponent of `‖x, y‖_P`
is `m + n − γ ≥ 0` and must dominate `η − γ`. The hypothesis holds whenever `ηᵢ ≤ γᵢ`, the case
of interest (Hairer assumes `η ≤ γ` in Propositions 6.9 and 6.16). Without it, the product lies
in `D^{γ, η ∧ γ}_P` (`Model.singularBoundOn_truncMul_min_inf`,
`Model.truncMul_mem_singularModelledDistributions_min_inf`).

Main statements:

* `Model.singularBoundOn_truncMul`: the bound
  `|||f₁ ⋆_γ f₂|||_{γ,η;S} ≤ c C₁ C₂ (1 + C_Γ)²` with `c = (3 + |ι|⁴) ‖⋆‖`, for every
  `γ ≤ (γ₁ + α₂) ∧ (γ₂ + α₁)` and `η ≤ (η₁ + α₂) ∧ (η₂ + α₁) ∧ (η₁ + η₂)` with `η ≤ γ`;
* `Model.singularBoundOn_truncMul_min`: Hairer's exponents;
* `Model.truncMul_mem_singularModelledDistributions(_min)`: `f₁ ⋆_γ f₂ ∈ D^{γ,η}_P`;
* `Model.singularBoundOn_truncMul_min_inf`,
  `Model.truncMul_mem_singularModelledDistributions_min_inf`: Hairer's exponents with no extra
  hypothesis, landing in `D^{γ, η ∧ γ}_P`.

No property of the distance function `ρ` is needed: every admissible pair has
`d(y, x) ≤ ‖x, y‖_P ≤ ‖x‖_P, ‖y‖_P`, and all factors are bounded through `‖x, y‖_P`.

Source: [Hai14] = arXiv:1303.5113v4, Proposition 6.12 and its proof, (6.10)–(6.12).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- The sup bound of `D^{γ,η}_P` evaluated with any weight `0 < w ≤ ‖x‖_P`, in every
coordinate. -/
theorem SingularBoundOn.abs_apply_le_weight {ρ : E → ℝ} {γ η C : ℝ} {S : Set E}
    {f : E → ι → ℝ} (hf : M.SingularBoundOn ρ γ η C S f) (hC : 0 ≤ C) {x : E}
    (hfT : f x ∈ lowerSubspace 𝒯.deg γ) (hx : x ∈ S) (hρ : 0 < ρ x) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ singularWeight ρ x) (i : ι) : |f x i| ≤ C * w ^ min (η - 𝒯.deg i) 0 := by
  by_cases hi : 𝒯.deg i < γ
  · refine (hf.1 x hx hρ i hi).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.rpow_le_rpow_of_nonpos hw0 hw (min_le_right _ _)
  · rw [hfT i (not_lt.1 hi), abs_zero]
    exact mul_nonneg hC (Real.rpow_nonneg hw0.le _)

theorem increment_apply_eq_zero_of_mem {γ : ℝ} {f : E → ι → ℝ} {x y : E}
    (hx : f x ∈ lowerSubspace 𝒯.deg γ) (hy : f y ∈ lowerSubspace 𝒯.deg γ) {i : ι}
    (hi : γ ≤ 𝒯.deg i) : (f y - M.gammaMap y x (f x)) i = 0 := by
  rw [Pi.sub_apply, hy i hi, (M.isGradedUnipotent_gammaMap y x).map_lowerSubspace hx i hi,
    sub_zero]

theorem increment_mem_of_mem {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V) {f : E → ι → ℝ}
    {x y : E} (hx : f x ∈ V) (hy : f y ∈ V) : f y - M.gammaMap y x (f x) ∈ V :=
  V.sub_mem hy (hV.invariant _ (M.gamma y x).2 _ hx)

end Model

end RegularityStructures

end
