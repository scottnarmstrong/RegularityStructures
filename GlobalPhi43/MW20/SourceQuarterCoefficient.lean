module

public import GlobalPhi43.MW20.SourceGlobalRadiusCoefficient

/-! Monotonicity in the radius of the actual local two-point supremum. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Reducing the actual two-point testing radius decreases the local norm. -/
theorem localTwoPointSup_mono_radius
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    {r s : ℝ} (hrs : r ≤ s) : localTwoPointSup U D r ≤ localTwoPointSup U D s := by
  have hall : ∀ x ∈ D, ∀ y ∈ D, ∀ (_ : pdist x y ≤ s),
      ENNReal.ofReal |U (x, y)| ≤ localTwoPointSup U D s := by
    simpa only [localTwoPointSup, iSup_le_iff] using
      (le_rfl : localTwoPointSup U D s ≤ localTwoPointSup U D s)
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply iSup_le
  intro hh
  exact hall x hx y hy (hh.trans hrs)

end GlobalPhi43.MW20
