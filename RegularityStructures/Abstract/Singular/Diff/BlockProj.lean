/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Slab.BlockProj
public import RegularityStructures.Abstract.WeightedSingularCubeTwoModels
public import RegularityStructures.Abstract.Model

/-!
# Block projection for the two-model singular bound

If both models commute with `blockProj A`, then `blockProj A` preserves the two-model bound
`|||f; g|||_{γ,η;S}` with the same constant (difference version of `SingularBoundOn.blockProj`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- **Block projection preserves the two-model singular bound** (same constant), when both
structure groups commute with `blockProj A`. -/
theorem SingularDiffBoundOn.blockProj {M₁ M₂ : Model 𝒯 K} {A : Finset ι}
    (hA₁ : ∀ x y τ, M₁.gammaMap x y (RegularityStructures.blockProj A τ) =
      RegularityStructures.blockProj A (M₁.gammaMap x y τ))
    (hA₂ : ∀ x y τ, M₂.gammaMap x y (RegularityStructures.blockProj A τ) =
      RegularityStructures.blockProj A (M₂.gammaMap x y τ))
    {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {f₁ f₂ : E → ι → ℝ}
    (h : M₁.SingularDiffBoundOn M₂ ρ γ η C S f₁ f₂) :
    M₁.SingularDiffBoundOn M₂ ρ γ η C S (fun x => RegularityStructures.blockProj A (f₁ x))
      (fun x => RegularityStructures.blockProj A (f₂ x)) := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · have e : RegularityStructures.blockProj A (f₁ x) i - RegularityStructures.blockProj A (f₂ x) i
        = RegularityStructures.blockProj A (f₁ x - f₂ x) i := by
      rw [map_sub]; rfl
    rw [e]
    exact (abs_blockProj_apply_le A _ i).trans (by simpa using h.1 x hx hρ i hi)
  · have e : (RegularityStructures.blockProj A (f₁ y) -
        M₁.gammaMap y x (RegularityStructures.blockProj A (f₁ x))) j -
        (RegularityStructures.blockProj A (f₂ y) -
        M₂.gammaMap y x (RegularityStructures.blockProj A (f₂ x))) j =
        RegularityStructures.blockProj A ((f₁ y - M₁.gammaMap y x (f₁ x)) -
          (f₂ y - M₂.gammaMap y x (f₂ x))) j := by
      rw [hA₁, hA₂]
      simp only [map_sub]
      rfl
    rw [e]
    exact (abs_blockProj_apply_le A _ j).trans (by simpa using h.2 x hx y hy hρx hρy hd j hj)

end Model

end RegularityStructures

end
