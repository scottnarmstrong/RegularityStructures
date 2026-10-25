/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductBounds
public import RegularityStructures.Abstract.Model

/-!
# Multiplication of modelled distributions

[Hai14, Theorem 4.7]: let `(V, W)` be sectors of regularities `α₁`, `α₂`, `f₁ ∈ D^{γ₁}(V)`,
`f₂ ∈ D^{γ₂}(W)` and `γ = (γ₁ + α₂) ∧ (γ₂ + α₁)`. If `(V, W)` is `γ`-regular, then
`f₁ ⋆_γ f₂ = Q_{<γ} (f₁ ⋆ f₂) ∈ D^γ` and
`|||f₁ ⋆_γ f₂|||_γ ≤ c |||f₁|||_{γ₁} |||f₂|||_{γ₂} (1 + ‖Γ‖)²`
with `c = (3 + |ι|⁴) ‖⋆‖` depending only on `𝒯` and `⋆` (`GradedProduct.truncMulConst`).

Main statements:

* `Model.modelledBoundOn_truncMul`: the bound on any set `S`, for every `γ ≤ (γ₁ + α₂) ∧ (γ₂ + α₁)`;
* `Model.modelledBoundOn_truncMul_min`: the statement with `γ = (γ₁ + α₂) ∧ (γ₂ + α₁)`;
* `Model.truncMul_mem_modelledDistributions`: `f₁ ⋆_γ f₂ ∈ D^γ`.

The model bound used is `GammaBoundOn γᵢ C_Γ S` for `i = 1, 2`; this is implied by Hairer's
`‖Γ‖_{γ₁ + γ₂; S}` when `γ₁, γ₂ ≥ 0`. In this formalisation `D^γ` has global bounds with no
restriction `d(y, x) ≤ 1`, so besides Hairer's argument for `d ≤ 1`
(`abs_truncMul_increment_le_of_le_one`) there is a separate argument for `d ≥ 1`
(`abs_truncMul_increment_le_of_one_le`), which also uses `γ`-regularity. Membership in `D^γ`
needs a global bound on `Γ` (the `Model` structure carries no analytic bounds).

Source: [Hai14] = arXiv:1303.5113v4, Theorem 4.7 and its proof, (4.3)–(4.6).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant `(3 + |ι|⁴) ‖⋆‖` of the product estimate [Hai14, Theorem 4.7]. -/
def RegularityStructure.GradedProduct.truncMulConst {𝒯 : RegularityStructure ι}
    (P : 𝒯.GradedProduct) : ℝ :=
  (3 + (Fintype.card ι : ℝ) ^ 4) * P.const

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem RegularityStructure.GradedProduct.const_le_truncMulConst {𝒯 : RegularityStructure ι}
    (P : 𝒯.GradedProduct) : P.const ≤ P.truncMulConst := by
  unfold RegularityStructure.GradedProduct.truncMulConst
  have h4 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ 4 := by positivity
  nlinarith [P.const_nonneg]

theorem RegularityStructure.GradedProduct.truncMulConst_nonneg {𝒯 : RegularityStructure ι}
    (P : 𝒯.GradedProduct) : 0 ≤ P.truncMulConst :=
  P.const_nonneg.trans P.const_le_truncMulConst

/-- The final arithmetic of the product estimate: `3 Z + |ι|⁴ Z G ≤ (3 + |ι|⁴) Z G` for
`Z ≥ 0`, `G ≥ 1`. -/
theorem three_add_card_pow_le {Z G N : ℝ} (hZ : 0 ≤ Z) (hG : 1 ≤ G) :
    Z + Z + Z + N ^ 4 * (Z * G) ≤ (3 + N ^ 4) * (Z * G) := by
  have hZG : Z ≤ Z * G := le_mul_of_one_le_right hZ hG
  have : (3 + N ^ 4) * (Z * G) = 3 * (Z * G) + N ^ 4 * (Z * G) := by ring
  rw [this]
  linarith

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

variable (P : 𝒯.GradedProduct)

/-- For a `γ`-regular pair: `Γ f₁ ⋆ Γ f₂ − Γ (f₁ ⋆_γ f₂) = ∑_{m + n ≥ γ} Γ Q_m f₁ ⋆ Γ Q_n f₂`
[Hai14, (4.5)]. -/
theorem mul_gammaMap_sub_gammaMap_truncMul_eq {V W : Submodule ℝ (ι → ℝ)}
    (hV : 𝒯.IsSector V) (hW : 𝒯.IsSector W) {γ : ℝ} (hreg : P.IsRegularPair V W γ)
    {f₁ f₂ : E → ι → ℝ} {x : E} (hf₁V : f₁ x ∈ V) (hf₂W : f₂ x ∈ W) (y : E) :
    P.mul (M.gammaMap y x (f₁ x)) (M.gammaMap y x (f₂ x)) -
        M.gammaMap y x (P.truncMul γ f₁ f₂ x) =
      ∑ m ∈ Finset.univ.image 𝒯.deg, ∑ n ∈ Finset.univ.image 𝒯.deg,
        if m + n < γ then 0 else
          P.mul (M.gammaMap y x (homogeneousProj 𝒯.deg m (f₁ x)))
            (M.gammaMap y x (homogeneousProj 𝒯.deg n (f₂ x))) :=
  hreg.mul_map_sub_map_lowerProj_mul hV.graded hW.graded (M.gamma y x).2 hf₁V hf₂W

end Model

end RegularityStructures

end
