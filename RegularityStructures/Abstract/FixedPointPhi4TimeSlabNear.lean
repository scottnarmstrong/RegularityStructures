/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointPhi4IntegrationNear
public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab

/-!
# The `Φ⁴₃` fixed point on `(0, T] × ℝ³`, near-pair `Γ`-bounds

The fixed-point part of [Hai14, Proposition 9.8] on `(0, T] × ℝ³`, for an operator `𝒦` that is a
parameter of the theorem with Theorem 7.1 bounds: for `T` below an explicit `fixedPointTime`,
`U = −𝒦(U³) + v` has a unique solution with `|||U|||_{γ₀,η₀;T} ≤ R₀ + 1`, for models whose
`Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ParabolicSpace}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup ParabolicSpace μ}
  {M : Model 𝒯 K} (P : 𝒯.GradedProduct) {V W V' : Submodule ℝ (ι → ℝ)}
  {α γ₀ η₀ η' η'' CΓ γ η γ' : ℝ}

/-- **Conditional on Theorem 7.1 bounds for the hypothesised operator `𝒦`:** the fixed-point part of
[Hai14, Proposition 9.8] on `(0, T] × ℝ³`. `𝒦` is a theorem parameter, not yet the heat-kernel
integration operator. The hypotheses are those
of `Model.exists_unique_phi4_slab_fixedPoint_of_integration_near` with `ρ = |t|^{1/2}`,
`S = (0, T] × ℝ³` and `𝔰₀ = 2`: for
`0 < T ≤ fixedPointTime (C (1 + |ι| C_Γ)) (((η_K ∧ γ₀) − η₀)/2) (3 c² (1 + C_Γ)⁴) 0 R₀ 2`,
`U = −𝒦(U³) + v` has a unique solution with `|||U|||_{γ₀,η₀;T} ≤ R₀ + 1`. -/
theorem exists_unique_phi4_timeSlab_fixedPoint_of_integration_near (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α) {T : ℝ}
    (hΓ₀ : M.GammaNearOn γ₀ CΓ (timeSlab T)) (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ (timeSlab T))
    (hCΓ : 0 ≤ CΓ) {γK ηK C R₀ : ℝ} (hΓK : M.GammaNearOn γK CΓ (timeSlab T))
    (hγK : γ₀ ≤ γK) (hηK : η₀ < ηK) (hηγ : η₀ < γ₀) (hC : 0 ≤ C) (hR₀ : 0 ≤ R₀) (hT : 0 < T)
    (hTT₀ : T ≤ fixedPointTime (C * (1 + Fintype.card ι * CΓ)) ((min ηK γ₀ - η₀) / 2)
      (3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) 0 R₀ 2)
    (𝒦₀ : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) → ParabolicSpace → ι → ℝ)
    (h𝒦₀T : ∀ g, ∀ x ∈ timeSlab T, 0 < timeZeroDist x → 𝒦₀ g x ∈ lowerSubspace 𝒯.deg γK)
    (h𝒦₀ : ∀ g, M.SingularBoundOn timeZeroDist γK ηK (C * ‖g‖) (timeSlab T) (𝒦₀ g))
    (h𝒦₀sup : ∀ g, ∀ x ∈ timeSlab T, 0 < timeZeroDist x → ∀ i, 𝒯.deg i < γK →
      |𝒦₀ g x i| ≤ C * ‖g‖ * singularWeight timeZeroDist x ^ (ηK - 𝒯.deg i))
    (𝒦 : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) →ₗ[ℝ]
      M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T))
    (h𝒦 : ∀ g, ∀ x ∈ timeSlab T, 0 < timeZeroDist x →
      (𝒦 g).val x = RegularityStructures.lowerProj 𝒯.deg γ₀ (𝒦₀ g x))
    (v : M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)) (hv : ‖v‖ ≤ R₀) :
    ∃! U : M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T),
      ‖U‖ ≤ R₀ + 1 ∧ U = -𝒦 (SlabSpace.cube P (γ₀ + α + α) η'' U) + v :=
  exists_unique_phi4_slab_fixedPoint_of_integration_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂
    hη'γ hη''₁ hη''₂ hη''₃ hη''γ hΓ₀ hΓ₁ hCΓ hΓK hγK hηK hηγ hC two_pos hR₀ hT hTT₀
    (fun _ hx _ => timeZeroDist_le_rpow_of_mem_timeSlab hx) 𝒦₀ h𝒦₀T h𝒦₀ h𝒦₀sup 𝒦 h𝒦 v hv

end Model

end RegularityStructures

end
