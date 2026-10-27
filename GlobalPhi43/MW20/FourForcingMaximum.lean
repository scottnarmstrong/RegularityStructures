module

public import GlobalPhi43.MW20.InteriorCubicMaximum

/-!
# The four forcing norms in MW20 (4.28)
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- A bounded actual absolute-value supremum is nonnegative on nonempty
source cylinders, with no regularity requirement on the field. -/
theorem sourceSup_nonneg_of_bddAbove (f : ParabolicSpace → ℝ) {S : ℝ}
    (hS : S ∈ Icc (0 : ℝ) (1 / 2))
    (hf : BddAbove ((fun z => |f z|) '' sourceCylinder S)) : 0 ≤ sourceSup f S := by
  obtain ⟨z, hz⟩ := sourceCylinder_nonempty hS
  exact (abs_nonneg _).trans (le_csSup hf ⟨z, hz, rfl⟩)

/-- The literal maximum of the four source forcing-norm cube roots. -/
@[expose] noncomputable def fourForcingRoot (A B C D : ParabolicSpace → ℝ) (S : ℝ) : ℝ :=
  max (max (sourceSup A S ^ (1 / 3 : ℝ)) (sourceSup B S ^ (1 / 3 : ℝ)))
    (max (sourceSup C S ^ (1 / 3 : ℝ)) (sourceSup D S ^ (1 / 3 : ℝ)))

end GlobalPhi43.MW20
