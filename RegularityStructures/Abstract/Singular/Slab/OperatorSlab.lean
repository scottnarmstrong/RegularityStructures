/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointSlabSpace
public import RegularityStructures.Abstract.FixedPointTruncation
public import RegularityStructures.Abstract.FixedPointShortTime

/-!
# From a singular-bound operator to a map of slab spaces

Let `F : E → ι → ℝ` satisfy the bound of `D^{γK,ηK}_P` on the slab `S` (`ρ > 0` on `S`), take values
in `T_{<γK}` and in a coordinate-closed subspace `V` on `S`. Then `Q_{<γ₀} F`, extended by zero off
`S`, lies in `slabModelledDistributions ρ V γ₀ η₀ S` whenever `γ₀ ≤ γK`, `η₀ ≤ min ηK γ₀`
(`indicator_lowerProj_mem_slabModelledDistributions`, using `SingularBoundOn.lowerProj`).
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι]

/-- A subspace spanned by basis vectors: `a ∈ V`, `a j ≠ 0` implies `e_j ∈ V`. -/
def IsCoordClosed (V : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lowerProj_mem_of_isCoordClosed {V : Submodule ℝ (ι → ℝ)} (hV : IsCoordClosed V)
    (deg : ι → ℝ) (γ : ℝ) {a : ι → ℝ} (ha : a ∈ V) : lowerProj deg γ a ∈ V := by
  have h : lowerProj deg γ a = ∑ j, lowerProj deg γ a j • (Pi.single j 1 : ι → ℝ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : lowerProj deg γ a j = 0
  · rw [hj, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (hV a ha j ?_)
    intro h0
    apply hj
    rw [lowerProj_apply]
    simp [h0]

namespace Model

omit [DecidableEq ι] in
theorem measurable_lowerProj (deg : ι → ℝ) (γ : ℝ) :
    Measurable (lowerProj deg γ : (ι → ℝ) → ι → ℝ) :=
  (lowerProj deg γ).continuous_of_finiteDimensional.measurable

end Model

end RegularityStructures

end
