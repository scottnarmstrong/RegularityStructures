/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularCube
public import RegularityStructures.Abstract.WeightedSingularProductNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.WeightedSingularCube`

The statements of `RegularityStructures.Abstract.WeightedSingularCube` that involve `Γ`-bounds, for
models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

variable (P : 𝒯.GradedProduct)

/-- **Triple products of singular modelled distributions** (two applications of
[Hai14, Proposition 6.12]):
`|||Q_{<γ₀+2α} (U₁ ⋆ (U₂ ⋆ U₃))|||_{γ₀+2α, η''; S} ≤ c² C₁ C₂ C₃ (1 + C_Γ)⁴`. -/
theorem singularBoundOn_truncTripleMul_near {V W : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) {α γ₀ η₀ η' η'' : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α) {ρ : E → ℝ} {S : Set E}
    {U₁ U₂ U₃ : E → ι → ℝ} {C₁ C₂ C₃ CΓ : ℝ} (hU₁V : ∀ x ∈ S, 0 < ρ x → U₁ x ∈ V)
    (hU₂V : ∀ x ∈ S, 0 < ρ x → U₂ x ∈ V) (hU₃V : ∀ x ∈ S, 0 < ρ x → U₃ x ∈ V)
    (hU₁T : ∀ x ∈ S, 0 < ρ x → U₁ x ∈ lowerSubspace 𝒯.deg γ₀)
    (hU₂T : ∀ x ∈ S, 0 < ρ x → U₂ x ∈ lowerSubspace 𝒯.deg γ₀)
    (hU₃T : ∀ x ∈ S, 0 < ρ x → U₃ x ∈ lowerSubspace 𝒯.deg γ₀)
    (hU₁ : M.SingularBoundOn ρ γ₀ η₀ C₁ S U₁) (hU₂ : M.SingularBoundOn ρ γ₀ η₀ C₂ S U₂)
    (hU₃ : M.SingularBoundOn ρ γ₀ η₀ C₃ S U₃) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hΓ₀ : M.GammaNearOn γ₀ CΓ S) (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S) (hCΓ : 0 ≤ CΓ) :
    M.SingularBoundOn ρ (γ₀ + α + α) η''
      (P.truncMulConst ^ 2 * C₁ * C₂ * C₃ * (1 + CΓ) ^ 4) S
      (P.truncTripleMul (γ₀ + α + α) U₁ U₂ U₃) := by
  have hinner := M.singularBoundOn_truncMul_near P hV hV hVα hVα le_rfl le_rfl hη'₁ hη'₁ hη'₂ hη'γ
    hreg₁ hU₂V hU₃V hU₂T hU₃T hU₂ hU₃ hC₂ hC₃ hΓ₀ hΓ₀ hCΓ
  have hinnerW : ∀ x ∈ S, 0 < ρ x → P.truncMul (γ₀ + α) U₂ U₃ x ∈ W := fun x hx hρ =>
    lowerProj_mem_of_graded hW.graded _ (hVVW _ (hU₂V x hx hρ) _ (hU₃V x hx hρ))
  have hc : 0 ≤ P.truncMulConst * C₂ * C₃ * (1 + CΓ) ^ 2 := by
    have := P.truncMulConst_nonneg
    positivity
  have houter := M.singularBoundOn_truncMul_near P hV hW hVα hWα (by linarith) (by linarith)
    hη''₁ (by linarith) hη''₃ hη''γ hreg₂ hU₁V hinnerW hU₁T
    (fun x _ _ => P.truncMul_mem_lowerSubspace _ _ _ x) hU₁ hinner hC₁ hc hΓ₀ hΓ₁ hCΓ
  refine (houter.congr M fun x hx hρ =>
    (P.truncTripleMul_eq_truncMul_truncMul hVα (hU₁V x hx hρ)).symm).mono M (le_of_eq ?_)
  ring

/-- The cube on a sector of regularity `α`:
`|||U³|||_{γ₀+2α, η''; S} ≤ c² C³ (1 + C_Γ)⁴` for `U ∈ D^{γ₀,η₀}_P(V)`. -/
theorem singularBoundOn_truncCube_near {V W : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) {α γ₀ η₀ η' η'' : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α) {ρ : E → ℝ} {S : Set E}
    {U : E → ι → ℝ} {C CΓ : ℝ} (hUV : ∀ x ∈ S, 0 < ρ x → U x ∈ V)
    (hUT : ∀ x ∈ S, 0 < ρ x → U x ∈ lowerSubspace 𝒯.deg γ₀)
    (hU : M.SingularBoundOn ρ γ₀ η₀ C S U) (hC : 0 ≤ C) (hΓ₀ : M.GammaNearOn γ₀ CΓ S)
    (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S) (hCΓ : 0 ≤ CΓ) :
    M.SingularBoundOn ρ (γ₀ + α + α) η'' (P.truncMulConst ^ 2 * C ^ 3 * (1 + CΓ) ^ 4) S
      (P.truncCube (γ₀ + α + α) U) := by
  refine (M.singularBoundOn_truncTripleMul_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
    hη''₁ hη''₂ hη''₃ hη''γ hUV hUV hUV hUT hUT hUT hU hU hU hC hC hC hΓ₀ hΓ₁ hCΓ).mono M
    (le_of_eq ?_)
  ring

/-- **Local Lipschitz bound for the cube on `D^{γ₀,η₀}_P`**: if `U, Ū ∈ D^{γ₀,η₀}_P(V)` on `S`
with constants `C`, `C̄` and `|||U − Ū|||_{γ₀,η₀;S} ≤ δ`, then
`|||U³ − Ū³|||_{γ₀+2α, η''; S} ≤ c² δ (C² + C̄ C + C̄²) (1 + C_Γ)⁴`. -/
theorem singularBoundOn_truncCube_sub_near {V W : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) {α γ₀ η₀ η' η'' : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α) {ρ : E → ℝ} {S : Set E}
    {U U' : E → ι → ℝ} {C C' δ CΓ : ℝ} (hUV : ∀ x ∈ S, 0 < ρ x → U x ∈ V)
    (hU'V : ∀ x ∈ S, 0 < ρ x → U' x ∈ V)
    (hUT : ∀ x ∈ S, 0 < ρ x → U x ∈ lowerSubspace 𝒯.deg γ₀)
    (hU'T : ∀ x ∈ S, 0 < ρ x → U' x ∈ lowerSubspace 𝒯.deg γ₀)
    (hU : M.SingularBoundOn ρ γ₀ η₀ C S U) (hU' : M.SingularBoundOn ρ γ₀ η₀ C' S U')
    (hδ : M.SingularBoundOn ρ γ₀ η₀ δ S (U - U')) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hδ0 : 0 ≤ δ)
    (hΓ₀ : M.GammaNearOn γ₀ CΓ S) (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S) (hCΓ : 0 ≤ CΓ) :
    M.SingularBoundOn ρ (γ₀ + α + α) η''
      (P.truncMulConst ^ 2 * δ * (C ^ 2 + C' * C + C' ^ 2) * (1 + CΓ) ^ 4) S
      (P.truncCube (γ₀ + α + α) U - P.truncCube (γ₀ + α + α) U') := by
  have hDV : ∀ x ∈ S, 0 < ρ x → (U - U') x ∈ V := fun x hx hρ =>
    V.sub_mem (hUV x hx hρ) (hU'V x hx hρ)
  have hDT : ∀ x ∈ S, 0 < ρ x → (U - U') x ∈ lowerSubspace 𝒯.deg γ₀ := fun x hx hρ =>
    Submodule.sub_mem _ (hUT x hx hρ) (hU'T x hx hρ)
  have h1 := M.singularBoundOn_truncTripleMul_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
    hη''₁ hη''₂ hη''₃ hη''γ hDV hUV hUV hDT hUT hUT hδ hU hU hδ0 hC hC hΓ₀ hΓ₁ hCΓ
  have h2 := M.singularBoundOn_truncTripleMul_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
    hη''₁ hη''₂ hη''₃ hη''γ hU'V hDV hUV hU'T hDT hUT hU' hδ hU hC' hδ0 hC hΓ₀ hΓ₁ hCΓ
  have h3 := M.singularBoundOn_truncTripleMul_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
    hη''₁ hη''₂ hη''₃ hη''γ hU'V hU'V hDV hU'T hU'T hDT hU' hU' hδ hC' hC' hδ0 hΓ₀ hΓ₁ hCΓ
  rw [P.truncCube_sub_truncCube]
  refine ((h1.add M h2).add M h3).mono M (le_of_eq ?_)
  ring

end Model

end RegularityStructures

end
