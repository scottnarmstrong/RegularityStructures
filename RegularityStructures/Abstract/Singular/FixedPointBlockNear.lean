/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointPhi4TimeSlabNear
public import RegularityStructures.Abstract.Singular.Slab.TimeSlabOperatorNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Singular.Slab.BlockOperator

/-!
# The `Φ⁴₃` slab fixed point for a block-projected operator, near-pair `Γ`-bounds

`phi4IntegrationOperatorNear` is the slab operator `g ↦ Q_{<γ₀} F ((blockProj A g).val)` into
`D^{γ₀,η₀}_P(V)`. The bounds on `F` are only required on block-projected inputs
`f = (blockProj A g).val`, with constant `C ‖blockProj A g‖`.
`exists_unique_phi4_timeSlab_fixedPoint_of_blockOperator_near` is the fixed-point theorem
`Model.exists_unique_phi4_timeSlab_fixedPoint_of_integration_near` for this operator.

This is the version for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ParabolicSpace}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup ParabolicSpace μ}

/-- The integration operator of the `Φ⁴₃` time-slab fixed-point theorem:
`g ↦ Q_{<γ₀} F ((blockProj A g).val)` (extended by zero off the slab), a linear map
`D^{γ̄,η''}_P → D^{γ₀,η₀}_P(V)`. The bounds on `F` are needed only on block-projected inputs. -/
def phi4IntegrationOperatorNear (M : Model 𝒯 K) (T : ℝ) {γb η'' : ℝ} (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (blockProj A τ) = blockProj A (M.gammaMap x y τ))
    (F : (ParabolicSpace → ι → ℝ) → ParabolicSpace → ι → ℝ)
    (hFadd : ∀ g h : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T),
      F (SlabSpace.blockProj A hA (g + h)).val =
        F (SlabSpace.blockProj A hA g).val + F (SlabSpace.blockProj A hA h).val)
    (hFsmul : ∀ (c : ℝ) (g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T)),
      F (SlabSpace.blockProj A hA (c • g)).val = c • F (SlabSpace.blockProj A hA g).val)
    {V : Submodule ℝ (ι → ℝ)} {γ₀ γK η₀ ηK C CΓ : ℝ} (hVc : IsCoordClosed V)
    (hmeas : ∀ g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T),
      Measurable ((timeSlab T).indicator (F (SlabSpace.blockProj A hA g).val)))
    (hV : ∀ g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T), ∀ x ∈ timeSlab T,
      F (SlabSpace.blockProj A hA g).val x ∈ V)
    (hT : ∀ g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T), ∀ x ∈ timeSlab T,
      F (SlabSpace.blockProj A hA g).val x ∈ lowerSubspace 𝒯.deg γK)
    (hB : ∀ g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T),
      M.SingularBoundOn timeZeroDist γK ηK (C * ‖SlabSpace.blockProj A hA g‖) (timeSlab T)
        (F (SlabSpace.blockProj A hA g).val))
    (hΓ : M.GammaNearOn γK CΓ (timeSlab T)) (hC : 0 ≤ C) (hCΓ : 0 ≤ CΓ) (hγ : γ₀ ≤ γK)
    (hη : η₀ ≤ min ηK γ₀) :
    M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T) →ₗ[ℝ]
      M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T) :=
  M.slabOfOperatorNear T (blockOperator A hA F hFadd hFsmul) hVc hmeas hV hT
    (fun g => (hB g).mono M (mul_le_mul_of_nonneg_left (SlabSpace.norm_blockProj_le A hA g) hC))
    hΓ hC hCΓ hγ hη

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ParabolicSpace}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup ParabolicSpace μ}
  {M : Model 𝒯 K} (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)}
  {α γ₀ η₀ η' η'' CΓ : ℝ}

/-- **The `Φ⁴₃` time-slab fixed-point theorem for the block-projected integration operator**
`𝒦 g = Q_{<γ₀} F ((blockProj A g).val)`. Compared with
`Model.exists_unique_phi4_timeSlab_fixedPoint_of_integration_near`, the operator `𝒦` is built from
`F`, and the bounds on `F` are only assumed for the block-projected inputs
`f = (blockProj A g).val` with constant `C ‖blockProj A g‖`. -/
theorem exists_unique_phi4_timeSlab_fixedPoint_of_blockOperator_near (hV : 𝒯.IsSector V)
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
    (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (blockProj A τ) = blockProj A (M.gammaMap x y τ))
    (F : (ParabolicSpace → ι → ℝ) → ParabolicSpace → ι → ℝ)
    (hFadd : ∀ g h : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      F (SlabSpace.blockProj A hA (g + h)).val =
        F (SlabSpace.blockProj A hA g).val + F (SlabSpace.blockProj A hA h).val)
    (hFsmul : ∀ (c : ℝ) (g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T)),
      F (SlabSpace.blockProj A hA (c • g)).val = c • F (SlabSpace.blockProj A hA g).val)
    (hVc : IsCoordClosed V)
    (hFmeas : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      Measurable ((timeSlab T).indicator (F (SlabSpace.blockProj A hA g).val)))
    (hFV : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T), ∀ x ∈ timeSlab T,
      F (SlabSpace.blockProj A hA g).val x ∈ V)
    (hFT : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T), ∀ x ∈ timeSlab T,
      F (SlabSpace.blockProj A hA g).val x ∈ lowerSubspace 𝒯.deg γK)
    (hFB : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      M.SingularBoundOn timeZeroDist γK ηK (C * ‖SlabSpace.blockProj A hA g‖) (timeSlab T)
        (F (SlabSpace.blockProj A hA g).val))
    (hFsup : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      ∀ x ∈ timeSlab T, 0 < timeZeroDist x → ∀ i, 𝒯.deg i < γK →
        |F (SlabSpace.blockProj A hA g).val x i| ≤
          C * ‖SlabSpace.blockProj A hA g‖ * singularWeight timeZeroDist x ^ (ηK - 𝒯.deg i))
    (v : M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)) (hv : ‖v‖ ≤ R₀) :
    ∃! U : M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T),
      ‖U‖ ≤ R₀ + 1 ∧ U = -(M.phi4IntegrationOperatorNear T A hA F hFadd hFsmul hVc hFmeas hFV hFT hFB
        hΓK hC hCΓ hγK (le_min hηK.le hηγ.le)) (SlabSpace.cube P (γ₀ + α + α) η'' U) + v := by
  refine exists_unique_phi4_timeSlab_fixedPoint_of_integration_near P hV hW hVα hWα hVVW hreg₁ hreg₂
    hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ hΓ₀ hΓ₁ hCΓ hΓK hγK hηK hηγ hC hR₀ hT hTT₀
    (blockOperator A hA F hFadd hFsmul) (fun g x hx _ => hFT g x hx)
    (fun g => (hFB g).mono M (mul_le_mul_of_nonneg_left (SlabSpace.norm_blockProj_le A hA g) hC))
    (fun g x hx hρ i hi => (hFsup g x hx hρ i hi).trans ?_)
    (M.phi4IntegrationOperatorNear T A hA F hFadd hFsmul hVc hFmeas hFV hFT hFB hΓK hC hCΓ hγK
      (le_min hηK.le hηγ.le))
    (fun g x hx hρ => val_slabOfOperator_of_mem_near g hx hρ) v hv
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (SlabSpace.norm_blockProj_le A hA g) hC)
      (Real.rpow_nonneg (singularWeight_pos hρ).le _)

end Model

end RegularityStructures

end
