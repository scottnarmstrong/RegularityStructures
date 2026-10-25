/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointPhi4Near
public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.WeightedSingularCubeNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Local well-posedness of `Φ⁴₃` for an integration operator, near-pair `Γ`-bounds

[Hai14, Proposition 9.8]: if `𝒦 = Q_{<γ₀} 𝒦₀` on the slab, where `𝒦₀ g ∈ D^{γ_K,η_K}_P` with
constant `C |||g|||` and the vanishing bound of order `η_K`, then for `T` below an explicit
`fixedPointTime` the equation `U = −𝒦(U³) + v` has a unique solution with
`|||U|||_{γ₀,η₀;T} ≤ R₀ + 1`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {S : Set E} (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)}
  {α γ₀ η₀ η' η'' CΓ : ℝ}

/-- **[Hai14, Proposition 9.8], local well-posedness, with the integration operator of
Theorem 7.1.** Under the hypotheses of `Model.singularBoundOn_truncCube_near` (sectors `V`, `W`,
exponents `η'`, `η''`), let `𝒦 = Q_{<γ₀} 𝒦₀` on the slab where `𝒦₀ g ∈ D^{γ_K,η_K}_P` with
constant `C |||g|||` and the vanishing bound of order `η_K`; let `γ₀ ≤ γ_K`, `η₀ < η_K`,
`η₀ < γ₀`, `‖Γ‖ ≤ C_Γ` (degrees `< γ_K`) and `ρ ≤ T^{1/𝔰₀}` on the slab, and `|||v||| ≤ R₀`. For
`0 < T ≤ fixedPointTime (C (1 + |ι| C_Γ)) (((η_K ∧ γ₀) − η₀)/𝔰₀) (3 c² (1 + C_Γ)⁴) 0 R₀ 2`
the equation `U = −𝒦(U³) + v` has a unique solution with `|||U|||_{γ₀,η₀;T} ≤ R₀ + 1`. -/
theorem exists_unique_phi4_slab_fixedPoint_of_integration_near (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α) (hΓ₀ : M.GammaNearOn γ₀ CΓ S)
    (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S) (hCΓ : 0 ≤ CΓ) {γK ηK C s R₀ T : ℝ}
    (hΓK : M.GammaNearOn γK CΓ S) (hγK : γ₀ ≤ γK) (hηK : η₀ < ηK) (hηγ : η₀ < γ₀)
    (hC : 0 ≤ C) (hs : 0 < s) (hR₀ : 0 ≤ R₀) (hT : 0 < T)
    (hTT₀ : T ≤ fixedPointTime (C * (1 + Fintype.card ι * CΓ)) ((min ηK γ₀ - η₀) / s)
      (3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) 0 R₀ 2)
    (hS : ∀ x ∈ S, 0 < ρ x → ρ x ≤ T ^ s⁻¹)
    (𝒦₀ : M.SlabSpace ρ ⊤ (γ₀ + α + α) η'' S → E → ι → ℝ)
    (h𝒦₀T : ∀ g, ∀ x ∈ S, 0 < ρ x → 𝒦₀ g x ∈ lowerSubspace 𝒯.deg γK)
    (h𝒦₀ : ∀ g, M.SingularBoundOn ρ γK ηK (C * ‖g‖) S (𝒦₀ g))
    (h𝒦₀sup : ∀ g, ∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γK →
      |𝒦₀ g x i| ≤ C * ‖g‖ * singularWeight ρ x ^ (ηK - 𝒯.deg i))
    (𝒦 : M.SlabSpace ρ ⊤ (γ₀ + α + α) η'' S →ₗ[ℝ] M.SlabSpace ρ V γ₀ η₀ S)
    (h𝒦 : ∀ g, ∀ x ∈ S, 0 < ρ x →
      (𝒦 g).val x = RegularityStructures.lowerProj 𝒯.deg γ₀ (𝒦₀ g x))
    (v : M.SlabSpace ρ V γ₀ η₀ S) (hv : ‖v‖ ≤ R₀) :
    ∃! U : M.SlabSpace ρ V γ₀ η₀ S,
      ‖U‖ ≤ R₀ + 1 ∧ U = -𝒦 (SlabSpace.cube P (γ₀ + α + α) η'' U) + v := by
  have hc := P.truncMulConst_nonneg
  have hF : ∀ R (u u' : M.SlabSpace ρ V γ₀ η₀ S), ‖u‖ ≤ R → ‖u'‖ ≤ R →
      ‖-SlabSpace.cube P (γ₀ + α + α) η'' u - -SlabSpace.cube P (γ₀ + α + α) η'' u'‖ ≤
        3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * (1 + R) ^ 2 * ‖u - u'‖ := by
    intro R u u' hu hu'
    rw [neg_sub_neg, norm_sub_rev]
    exact SlabSpace.norm_cube_sub_cube_le_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁
      hη''₂ hη''₃ hη''γ hΓ₀ hΓ₁ hCΓ R u u' hu hu'
  have hF0 : ‖-SlabSpace.cube P (γ₀ + α + α) η'' (0 : M.SlabSpace ρ V γ₀ η₀ S)‖ ≤ 0 := by
    rw [SlabSpace.cube_zero_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ
      hΓ₀ hΓ₁ hCΓ, neg_zero, norm_zero]
  obtain ⟨U, hU, huniq⟩ := exists_unique_slab_fixedPoint_of_integration_near hγK hηK hηγ hC hCΓ hs
    (by positivity) le_rfl hR₀ hT hTT₀ hS hΓK 𝒦₀ h𝒦₀T h𝒦₀ h𝒦₀sup 𝒦 h𝒦
    (fun u => -SlabSpace.cube P (γ₀ + α + α) η'' u) hF hF0 v hv
  refine ⟨U, ⟨hU.1, by rw [← map_neg]; exact hU.2⟩, fun U' hU' => huniq U' ⟨hU'.1, ?_⟩⟩
  rw [map_neg]
  exact hU'.2

end Model

end RegularityStructures

end
