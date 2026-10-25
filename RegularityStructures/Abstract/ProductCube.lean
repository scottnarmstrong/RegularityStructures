/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductDefs

/-!
# Triple products and cubes of modelled distributions

The nonlinearity of Φ⁴₃ is `U ↦ Q_{<γ} (U ⋆ U ⋆ U)`. For a sector `V` of regularity `α` and a
sector `W ⊇ V ⋆ V` of regularity `2α`, two applications of [Hai14, Theorem 4.7] give: if
`U₁, U₂, U₃ ∈ D^{γ₀}(V)`, `(V, V)` is `(γ₀ + α)`-regular and `(V, W)` is `(γ₀ + 2α)`-regular, then
`Q_{<γ₀+2α} (U₁ ⋆ (U₂ ⋆ U₃)) ∈ D^{γ₀+2α}` with
`|||Q_{<γ₀+2α} (U₁ ⋆ (U₂ ⋆ U₃))||| ≤ c² C₁ C₂ C₃ (1 + C_Γ)⁴`
(`Model.modelledBoundOn_truncTripleMul`).
The inner product needs no truncation of its own: `Q_{<γ₀+2α} (U₁ ⋆ Q_{<γ₀+α} (U₂ ⋆ U₃))` equals
`Q_{<γ₀+2α} (U₁ ⋆ (U₂ ⋆ U₃))` because `U₁` has no components below `α`
(`GradedProduct.lowerProj_mul_lowerProj_of_le`).

Consequences for the cube `U³ = Q_{<γ₀+2α} (U ⋆ (U ⋆ U))` (`GradedProduct.truncCube`): the bound
`c² C³ (1 + C_Γ)⁴` (`Model.modelledBoundOn_truncCube`), membership in `D^{γ₀+2α}`
(`Model.truncCube_mem_modelledDistributions`) and the local Lipschitz bound
`|||U³ − Ū³||| ≤ c² δ (C² + C C̄ + C̄²) (1 + C_Γ)⁴` (`Model.modelledBoundOn_truncCube_sub`).

Source: [Hai14] = arXiv:1303.5113v4, Theorem 4.7, Remark 4.8 and §9 (Φ⁴₃).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RegularityStructure.GradedProduct

variable {𝒯 : RegularityStructure ι}

/-- The truncated triple product `Q_{<γ} (U₁(x) ⋆ (U₂(x) ⋆ U₃(x)))`. -/
def truncTripleMul (P : 𝒯.GradedProduct) {E : Type*} (γ : ℝ) (U₁ U₂ U₃ : E → ι → ℝ) :
    E → ι → ℝ :=
  fun x => lowerProj 𝒯.deg γ (P.mul (U₁ x) (P.mul (U₂ x) (U₃ x)))

/-- The truncated cube `Q_{<γ} (U(x) ⋆ (U(x) ⋆ U(x)))`, the nonlinearity of Φ⁴₃. -/
def truncCube (P : 𝒯.GradedProduct) {E : Type*} (γ : ℝ) (U : E → ι → ℝ) : E → ι → ℝ :=
  P.truncTripleMul γ U U U

end RegularityStructure.GradedProduct

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RegularityStructure.GradedProduct

variable {𝒯 : RegularityStructure ι} (P : 𝒯.GradedProduct)

/-- `Q_{<γ} (a ⋆ b) = 0` if `a` has no components below `α`, `b` none below `β`, and
`γ ≤ α + β`. -/
theorem lowerProj_mul_eq_zero {a b : ι → ℝ} {α β γ : ℝ} (ha : ∀ i, 𝒯.deg i < α → a i = 0)
    (hb : ∀ j, 𝒯.deg j < β → b j = 0) (h : γ ≤ α + β) : lowerProj 𝒯.deg γ (P.mul a b) = 0 := by
  funext k
  rw [lowerProj_apply, Pi.zero_apply]
  split_ifs with hk
  · have hle : |P.mul a b k| ≤ P.const * 0 := P.abs_mul_apply_le le_rfl fun i j hij => by
      by_cases hi : 𝒯.deg i < α
      · rw [ha i hi, abs_zero, zero_mul]
      · rw [hb j (by linarith [not_lt.1 hi]), abs_zero, mul_zero]
    rw [mul_zero] at hle
    exact abs_nonpos_iff.1 hle
  · rfl

/-- `Q_{<γ} (a ⋆ Q_{<γ'} b) = Q_{<γ} (a ⋆ b)` if `a` has no components below `α` and
`γ ≤ γ' + α`. -/
theorem lowerProj_mul_lowerProj_of_le {a b : ι → ℝ} {α γ γ' : ℝ}
    (ha : ∀ i, 𝒯.deg i < α → a i = 0) (h : γ ≤ γ' + α) :
    lowerProj 𝒯.deg γ (P.mul a (lowerProj 𝒯.deg γ' b)) = lowerProj 𝒯.deg γ (P.mul a b) := by
  have hrem : lowerProj 𝒯.deg γ (P.mul a (b - lowerProj 𝒯.deg γ' b)) = 0 := by
    refine P.lowerProj_mul_eq_zero ha (β := γ') (fun j hj => ?_) (by linarith)
    rw [Pi.sub_apply, lowerProj_apply_of_lt hj, sub_self]
  rw [map_sub, map_sub] at hrem
  exact (sub_eq_zero.1 hrem).symm

theorem truncTripleMul_sub_left {E : Type*} (γ : ℝ) (U₁ U₁' U₂ U₃ : E → ι → ℝ) :
    P.truncTripleMul γ (U₁ - U₁') U₂ U₃ =
      P.truncTripleMul γ U₁ U₂ U₃ - P.truncTripleMul γ U₁' U₂ U₃ := by
  funext x
  simp [truncTripleMul, map_sub]

theorem truncTripleMul_sub_middle {E : Type*} (γ : ℝ) (U₁ U₂ U₂' U₃ : E → ι → ℝ) :
    P.truncTripleMul γ U₁ (U₂ - U₂') U₃ =
      P.truncTripleMul γ U₁ U₂ U₃ - P.truncTripleMul γ U₁ U₂' U₃ := by
  funext x
  simp [truncTripleMul, map_sub]

theorem truncTripleMul_sub_right {E : Type*} (γ : ℝ) (U₁ U₂ U₃ U₃' : E → ι → ℝ) :
    P.truncTripleMul γ U₁ U₂ (U₃ - U₃') =
      P.truncTripleMul γ U₁ U₂ U₃ - P.truncTripleMul γ U₁ U₂ U₃' := by
  funext x
  simp [truncTripleMul, map_sub]

/-- `U³ − Ū³ = (U − Ū) ⋆ U ⋆ U + Ū ⋆ (U − Ū) ⋆ U + Ū ⋆ Ū ⋆ (U − Ū)` (truncated). -/
theorem truncCube_sub_truncCube {E : Type*} (γ : ℝ) (U U' : E → ι → ℝ) :
    P.truncCube γ U - P.truncCube γ U' =
      P.truncTripleMul γ (U - U') U U + P.truncTripleMul γ U' (U - U') U +
        P.truncTripleMul γ U' U' (U - U') := by
  rw [truncCube, truncCube, P.truncTripleMul_sub_left, P.truncTripleMul_sub_middle,
    P.truncTripleMul_sub_right]
  abel

/-- On a sector of regularity `α`, `Q_{<γ₀+2α} (U₁ ⋆ (U₂ ⋆ U₃)) = U₁ ⋆_{γ₀+2α} (U₂ ⋆_{γ₀+α} U₃)`. -/
theorem truncTripleMul_eq_truncMul_truncMul {E : Type*} {V : Submodule ℝ (ι → ℝ)} {α γ₀ : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α) {U₁ U₂ U₃ : E → ι → ℝ} {x : E}
    (hU₁ : U₁ x ∈ V) :
    P.truncTripleMul (γ₀ + α + α) U₁ U₂ U₃ x =
      P.truncMul (γ₀ + α + α) U₁ (P.truncMul (γ₀ + α) U₂ U₃) x :=
  (P.lowerProj_mul_lowerProj_of_le (fun _i hi =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα hU₁ hi) le_rfl).symm

end RegularityStructure.GradedProduct

end RegularityStructures

end
