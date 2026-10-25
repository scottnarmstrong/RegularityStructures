/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute.Lemma516
public import RegularityStructures.Abstract.Integration.Sector.Coeff
public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Abstract.Integration.SectorLocal
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Hairer's Lemma 5.16 for a sector `V` of degrees `> -2`

Sector versions of `Model.kRegular_regPi_single`, `realGerm_eq`, `Model.regPi_integral_add_jMap`
and `Model.gammaMap_integral_add_jMap` ([Hai14, Remark 5.10, proof of Lemma 5.16]). The global
hypothesis "every homogeneity below `γ` exceeds `-2`" is replaced by the same hypothesis for
the basis vectors `e_j ∈ V` only (`hdeg`), and the polynomial-order hypothesis `hN'` is only
required for `e_j ∈ V`. The only basis vectors `e_j` that occur are those of `V`, because
`Γ_{xy} e_i ∈ V` for `e_i ∈ V` (`IsSector.invariant`, `basis_mem`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {V : Submodule ℝ (ι → ℝ)}

/-- The degrees `a ≤ deg i` of basis vectors of `V` below `γ` are `> -2` if those of all basis
vectors of `V` below `γ` are. -/
theorem degreesBelowLeIn_bounds_two {γ : ℝ}
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j) (i : ι) :
    ∀ a ∈ 𝒯.degreesBelowLeIn V γ (𝒯.deg i), -2 < a ∧ a ≤ 𝒯.deg i := by
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
  obtain ⟨j, hjV, hj, rfl⟩ := (𝒯.mem_degreesBelowIn V).1 ha1
  exact ⟨hdeg j hjV hj, ha2⟩

end RegularityStructures

end
