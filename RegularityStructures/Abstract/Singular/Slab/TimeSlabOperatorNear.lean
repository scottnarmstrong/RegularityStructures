/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.Singular.Slab.OperatorSlabNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab

/-!
# The slab operator `g ↦ Q_{<γ₀} 𝒦₀' g`, near-pair `Γ`-bounds

The linear map `slabOfOperatorNear` from `D^{γ̄,η''}_P` into `D^{γ₀,η₀}_P(V)` on `(0, T] × ℝ³`,
given by `Q_{<γ₀} 𝒦₀' g` on the slab and `0` off it, and its evaluation on the slab, which is the
hypothesis on `𝒦` of `Model.exists_unique_phi4_timeSlab_fixedPoint_of_integration_near`, for models
whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ParabolicSpace}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup ParabolicSpace μ}

/-- The linear map `g ↦ Q_{<γ₀} 𝒦₀' g` (extended by zero off the slab) from `D^{γ̄,η''}_P` into
`D^{γ₀,η₀}_P(V)` on `(0, T] × ℝ³`. -/
def slabOfOperatorNear (M : Model 𝒯 K) (T : ℝ) {V : Submodule ℝ (ι → ℝ)} {γb η'' γ₀ γK η₀ ηK C CΓ : ℝ}
    (𝒦₀' : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T) →ₗ[ℝ] (ParabolicSpace → ι → ℝ))
    (hVc : IsCoordClosed V)
    (hmeas : ∀ g, Measurable ((timeSlab T).indicator (𝒦₀' g)))
    (hV : ∀ g, ∀ x ∈ timeSlab T, 𝒦₀' g x ∈ V)
    (hT : ∀ g, ∀ x ∈ timeSlab T, 𝒦₀' g x ∈ lowerSubspace 𝒯.deg γK)
    (hB : ∀ g, M.SingularBoundOn timeZeroDist γK ηK (C * ‖g‖) (timeSlab T) (𝒦₀' g))
    (hΓ : M.GammaNearOn γK CΓ (timeSlab T)) (hC : 0 ≤ C) (hCΓ : 0 ≤ CΓ) (hγ : γ₀ ≤ γK)
    (hη : η₀ ≤ min ηK γ₀) :
    M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T) →ₗ[ℝ]
      M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T) where
  toFun g := SlabSpace.mk ((timeSlab T).indicator (fun x => lowerProj 𝒯.deg γ₀ (𝒦₀' g x)))
    (M.indicator_lowerProj_mem_slabModelledDistributions_near
      (fun _ hx => timeZeroDist_pos_of_mem_timeSlab hx) hVc (hmeas g) (hV g) (hT g) (hB g) hΓ
      (mul_nonneg hC (norm_nonneg g)) hCΓ hγ hη)
  map_add' g h := by
    ext x
    by_cases hx : x ∈ timeSlab T <;> simp [hx, map_add]
  map_smul' c g := by
    ext x
    by_cases hx : x ∈ timeSlab T <;> simp [hx, map_smul]

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ParabolicSpace}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup ParabolicSpace μ}
  {M : Model 𝒯 K} {T : ℝ} {V : Submodule ℝ (ι → ℝ)} {γb η'' γ₀ γK η₀ ηK C CΓ : ℝ}
  {𝒦₀' : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T) →ₗ[ℝ] (ParabolicSpace → ι → ℝ)}
  {hVc : IsCoordClosed V}
  {hmeas : ∀ g, Measurable ((timeSlab T).indicator (𝒦₀' g))}
  {hV : ∀ g, ∀ x ∈ timeSlab T, 𝒦₀' g x ∈ V}
  {hT : ∀ g, ∀ x ∈ timeSlab T, 𝒦₀' g x ∈ lowerSubspace 𝒯.deg γK}
  {hB : ∀ g, M.SingularBoundOn timeZeroDist γK ηK (C * ‖g‖) (timeSlab T) (𝒦₀' g)}
  {hΓ : M.GammaNearOn γK CΓ (timeSlab T)} {hC : 0 ≤ C} {hCΓ : 0 ≤ CΓ} {hγ : γ₀ ≤ γK}
  {hη : η₀ ≤ min ηK γ₀}

/-- The underlying function of `slabOfOperatorNear`: `Q_{<γ₀} 𝒦₀' g` on the slab, `0` off it. -/
theorem val_slabOfOperator_near (g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T)) :
    (M.slabOfOperatorNear T 𝒦₀' hVc hmeas hV hT hB hΓ hC hCΓ hγ hη g).val =
      (timeSlab T).indicator (fun x => lowerProj 𝒯.deg γ₀ (𝒦₀' g x)) :=
  rfl

/-- The `h𝒦` hypothesis of `Model.exists_unique_phi4_timeSlab_fixedPoint_of_integration_near`. -/
theorem val_slabOfOperator_of_mem_near (g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T))
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) (_hρ : 0 < timeZeroDist x) :
    (M.slabOfOperatorNear T 𝒦₀' hVc hmeas hV hT hB hΓ hC hCΓ hγ hη g).val x =
      lowerProj 𝒯.deg γ₀ (𝒦₀' g x) := by
  rw [val_slabOfOperator_near, indicator_of_mem hx]

end Model

end RegularityStructures

end
