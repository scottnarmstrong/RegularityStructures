/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Slab.OperatorSlab
public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.Singular.Slab.OperatorSlab`

The statements of `RegularityStructures.Abstract.Singular.Slab.OperatorSlab` that involve
`Γ`-bounds, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι]

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- `Q_{<γ₀} F`, extended by zero off `S`, is a singular modelled distribution on the slab. -/
theorem indicator_lowerProj_mem_slabModelledDistributions_near {ρ : E → ℝ} {S : Set E}
    {V : Submodule ℝ (ι → ℝ)} {γ₀ γK η₀ ηK C CΓ : ℝ} {F : E → ι → ℝ}
    (hρ : ∀ x ∈ S, 0 < ρ x) (hVc : IsCoordClosed V)
    (hmeas : Measurable (S.indicator F)) (hV : ∀ x ∈ S, F x ∈ V)
    (hT : ∀ x ∈ S, F x ∈ lowerSubspace 𝒯.deg γK) (hB : M.SingularBoundOn ρ γK ηK C S F)
    (hΓ : M.GammaNearOn γK CΓ S) (hC : 0 ≤ C) (hCΓ : 0 ≤ CΓ) (hγ : γ₀ ≤ γK)
    (hη : η₀ ≤ min ηK γ₀) :
    S.indicator (fun x => lowerProj 𝒯.deg γ₀ (F x)) ∈
      M.slabModelledDistributions ρ V γ₀ η₀ S := by
  have hind : S.indicator (fun x => lowerProj 𝒯.deg γ₀ (F x)) =
      fun x => lowerProj 𝒯.deg γ₀ (S.indicator F x) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  refine ⟨?_, fun x hx _ => ?_, fun x hx => ?_, ?_⟩
  · rw [hind]
    exact (measurable_lowerProj 𝒯.deg γ₀).comp hmeas
  · rw [indicator_of_mem hx]
    exact Submodule.mem_inf.2 ⟨lowerProj_mem_of_isCoordClosed hVc _ _ (hV x hx), lowerProj_mem _⟩
  · exact indicator_of_notMem (fun h => hx ⟨h, hρ x h⟩) _
  · refine ⟨C * (1 + Fintype.card ι * CΓ), ?_⟩
    have h1 := (hB.lowerProj_near M (fun x hx _ => hT x hx) hγ hΓ hC hCΓ).mono_exponent M hη
      (by positivity)
    exact h1.congr M fun x hx _ =>
      (indicator_of_mem hx (fun x => lowerProj 𝒯.deg γ₀ (F x))).symm

end Model

end RegularityStructures

end
