/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SectionDifferentials
public import GlobalPhi43.Local.SpatialOperatorBound
public import GlobalPhi43.MW20.CylinderSup

/-! Finite derivative bounds are derived from the standing local smoothness
and compact carrier. These bounds are used only to justify absorption. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff

theorem isCompact_closure_sourceCylinder {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (closure (sourceCylinder r)) := by
  have hc : IsCompact sourceClosedCylinder := isCompact_Icc
  exact hc.of_isClosed_subset isClosed_closure
    (closure_minimal (sourceCylinder_subset_closed hr) isClosed_Icc)

/-- One finite constant bounds both derivative fields on the entire compact
pair carrier. No derivative allowance is added to the Schauder data. -/
theorem exists_compact_section_bound (U : GermPoint → ℝ) (K : Set GermPoint)
    (hK : IsCompact K) (hU : ∀ p ∈ K, ContDiffAt ℝ ∞ U p) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ p ∈ K,
      |sectionTimeDerivative U p| ≤ S ∧ ‖sectionSpaceHessian U p‖ ≤ S := by
  have ht : ContinuousOn (sectionTimeDerivative U) K :=
    fun p hp => (sectionTimeDerivative_contDiffAt U p (hU p hp)).continuousAt.continuousWithinAt
  have hs : ContinuousOn (fun p => ∑ i : Fin 3, ∑ j : Fin 3,
      |sectionSpaceHessian U p (Pi.single i 1) (Pi.single j 1)|) K := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _ p hp
    exact (((sectionSpaceHessian_contDiffAt U p (hU p hp)).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).continuousAt.abs.continuousWithinAt
  obtain ⟨a, ha⟩ := (hK.image_of_continuousOn ht.abs).bddAbove
  obtain ⟨b, hb⟩ := (hK.image_of_continuousOn hs).bddAbove
  refine ⟨max 0 (max a b), le_max_left _ _, fun p hp => ?_⟩
  constructor
  · exact (ha ⟨p, hp, rfl⟩).trans ((le_max_left a b).trans (le_max_right 0 (max a b)))
  · exact (spatial_hessian_norm_le_sum _).trans
      ((hb ⟨p, hp, rfl⟩).trans ((le_max_right a b).trans (le_max_right 0 (max a b))))

/-- The finite Taylor constant follows from smoothness on a neighbourhood
of the exact closed source cylinder squared, without a global extension. -/
theorem exists_source_section_bound (U : GermPoint → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ p ∈ closure (sourceCylinder r) ×ˢ closure (sourceCylinder r),
      |sectionTimeDerivative U p| ≤ S ∧ ‖sectionSpaceHessian U p‖ ≤ S := by
  obtain ⟨O, hO, hKO, hs⟩ := hU
  apply exists_compact_section_bound U _
    ((isCompact_closure_sourceCylinder hr).prod (isCompact_closure_sourceCylinder hr))
  intro p hp
  exact hs.contDiffAt (hO.mem_nhds (hKO hp))

end GlobalPhi43.Local
