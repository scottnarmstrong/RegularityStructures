/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SectorLocal

/-!
# Coefficients of `J(x)` and `N_γ f` with sector exponents

Sector versions of the bounds on the coefficients `jCoeff` and `nCoeff`: the
degree hypothesis `−4 < deg j` is only required for basis vectors `e_j ∈ V`, the exponent sets
are `degreesBelowLeIn V γ (deg i)` and `insert γ (degreesBelowIn V γ)`, and the constants
`jCoeffConstIn`, `nCoeffConstIn` are built from them. The coefficients `jCoeff`, `nCoeff`
themselves do not depend on `V`.

Source: [Hai14] = arXiv:1303.5113v4, (5.11), (5.16), proof of Theorem 5.12.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {V : Submodule ℝ (ι → ℝ)}

/-- The exponent set condition: all degrees `a ≤ deg i` of basis vectors of `V` below `γ` exceed
`-4` if the basis vectors of `V` below `γ` do. -/
theorem degreesBelowLeIn_bounds (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) {γ : ℝ}
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -4 < 𝒯.deg j) (i : ι) :
    ∀ a ∈ 𝒯.degreesBelowLeIn V γ (𝒯.deg i), -4 < a ∧ a ≤ 𝒯.deg i := by
  intro a ha
  rw [RegularityStructure.degreesBelowLeIn, Finset.mem_filter] at ha
  obtain ⟨j, hjV, hj, rfl⟩ := (𝒯.mem_degreesBelowIn V).1 ha.1
  exact ⟨hdeg j hjV hj, ha.2⟩

end RegularityStructures

end
