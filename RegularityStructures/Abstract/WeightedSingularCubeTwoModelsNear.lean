/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularCubeTwoModels
public import RegularityStructures.Abstract.WeightedSingularCubeNear
public import RegularityStructures.Abstract.WeightedSingularProductNear
public import RegularityStructures.Abstract.WeightedSingularTwoModelsNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.WeightedSingularCubeTwoModels`

The statements of `RegularityStructures.Abstract.WeightedSingularCubeTwoModels` that involve
`Γ`-bounds, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

variable (M₁ M₂ : Model 𝒯 K) (P : 𝒯.GradedProduct)

/-- **The cube on `D^{γ,η}_P` for two models**:
`|||U³; Ū³|||_{γ₀+2α, η''; S} ≤ c² (3 C² δ + 4 C³ δ_Γ) (1 + C_Γ)⁴`, under the hypotheses of
`Model.singularBoundOn_truncCube_near` for both models. -/
theorem singularDiffBoundOn_truncCube_near {V W : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) {α γ₀ η₀ η' η'' : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α) {ρ : E → ℝ} {S : Set E}
    {U U' : E → ι → ℝ} {C δ CΓ δΓ : ℝ} (hUV : ∀ x ∈ S, 0 < ρ x → U x ∈ V)
    (hU'V : ∀ x ∈ S, 0 < ρ x → U' x ∈ V)
    (hUT : ∀ x ∈ S, 0 < ρ x → U x ∈ lowerSubspace 𝒯.deg γ₀)
    (hU'T : ∀ x ∈ S, 0 < ρ x → U' x ∈ lowerSubspace 𝒯.deg γ₀)
    (hU : M₁.SingularBoundOn ρ γ₀ η₀ C S U) (hU' : M₂.SingularBoundOn ρ γ₀ η₀ C S U')
    (hδ : M₁.SingularDiffBoundOn M₂ ρ γ₀ η₀ δ S U U') (hC : 0 ≤ C) (hδ0 : 0 ≤ δ)
    (hΓ₁₀ : M₁.GammaNearOn γ₀ CΓ S) (hΓ₁₁ : M₁.GammaNearOn (γ₀ + α) CΓ S)
    (hΓ₂₀ : M₂.GammaNearOn γ₀ CΓ S) (hΓ₂₁ : M₂.GammaNearOn (γ₀ + α) CΓ S)
    (hΓd₀ : M₁.GammaDiffNearOn M₂ γ₀ δΓ S) (hΓd₁ : M₁.GammaDiffNearOn M₂ (γ₀ + α) δΓ S)
    (hCΓ : 0 ≤ CΓ) (hδΓ : 0 ≤ δΓ) :
    M₁.SingularDiffBoundOn M₂ ρ (γ₀ + α + α) η''
      (P.truncMulConst ^ 2 * (3 * C ^ 2 * δ + 4 * C ^ 3 * δΓ) * (1 + CΓ) ^ 4) S
      (P.truncCube (γ₀ + α + α) U) (P.truncCube (γ₀ + α + α) U') := by
  have hc := P.truncMulConst_nonneg
  -- the inner products and their comparison
  have hin₁ := M₁.singularBoundOn_truncMul_near P hV hV hVα hVα le_rfl le_rfl hη'₁ hη'₁ hη'₂ hη'γ
    hreg₁ hUV hUV hUT hUT hU hU hC hC hΓ₁₀ hΓ₁₀ hCΓ
  have hinδ := M₁.singularDiffBoundOn_truncMul_near M₂ P hV hV hVα hVα le_rfl le_rfl hη'₁ hη'₁ hη'₂
    hη'γ hreg₁ hUV hU'V hUV hU'V hUT hU'T hUT hU'T hU hU' hU hδ hδ hC hC hδ0 hδ0 hΓ₁₀ hΓ₂₀
    hΓ₂₀ hΓd₀ hΓd₀ hCΓ hδΓ
  have hinW₁ : ∀ x ∈ S, 0 < ρ x → P.truncMul (γ₀ + α) U U x ∈ W := fun x hx hρ =>
    lowerProj_mem_of_graded hW.graded _ (hVVW _ (hUV x hx hρ) _ (hUV x hx hρ))
  have hinW₂ : ∀ x ∈ S, 0 < ρ x → P.truncMul (γ₀ + α) U' U' x ∈ W := fun x hx hρ =>
    lowerProj_mem_of_graded hW.graded _ (hVVW _ (hU'V x hx hρ) _ (hU'V x hx hρ))
  have hC' : 0 ≤ P.truncMulConst * C * C * (1 + CΓ) ^ 2 := by positivity
  have hδ' : 0 ≤ P.truncMulConst * (δ * C + C * δ + 2 * C * C * δΓ) * (1 + CΓ) ^ 2 := by
    positivity
  -- the outer products
  have hout := M₁.singularDiffBoundOn_truncMul_near M₂ P hV hW hVα hWα (by linarith) (by linarith)
    hη''₁ (by linarith) hη''₃ hη''γ hreg₂ hUV hU'V hinW₁ hinW₂ hUT hU'T
    (fun x _ _ => P.truncMul_mem_lowerSubspace _ _ _ x)
    (fun x _ _ => P.truncMul_mem_lowerSubspace _ _ _ x) hU hU' hin₁ hδ hinδ hC hC' hδ0 hδ'
    hΓ₁₁ hΓ₂₀ hΓ₂₁ hΓd₀ hΓd₁ hCΓ hδΓ
  refine (hout.congr
    (fun x hx hρ => (P.truncTripleMul_eq_truncMul_truncMul hVα (hUV x hx hρ)).symm)
    (fun x hx hρ => (P.truncTripleMul_eq_truncMul_truncMul hVα (hU'V x hx hρ)).symm)).mono
    (le_of_eq ?_)
  ring

end Model

end RegularityStructures

end
