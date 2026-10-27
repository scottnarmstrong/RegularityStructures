module

public import GlobalPhi43.MW20.LocalSourceHolder
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.ScalarSupNorm

/-!
# Actual scalar testing norms from radius-local mixed-domain norms
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- A testing set of diameter at most L uses only the actual radius-L
source quotient supremum; its finiteness is retained explicitly. -/
theorem scalarHolderSeminorm_le_local_holder_on_diameter
    (f : ParabolicSpace → ℝ) {D E : Set ParabolicSpace} {a L : ℝ}
    (hED : E ⊆ D) (hL1 : L ≤ 1)
    (hb : BddAbove (localSourceHolderValues f a D L))
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, Local.pdist x y ≤ L) :
    scalarHolderSeminorm f E a ≤ ENNReal.ofReal (localSourceHolder f a D L) := by
  simp only [scalarHolderSeminorm, iSup_le_iff]
  intro x hx y hy hne
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) a)).2
    (localSourceHolder_increment hb (hED hx) (hED hy) (hdiam x hx y hy) hL1)

/-- The literal finite scalar norm value obeys the same actual source budget. -/
theorem scalarHolderSeminorm_toReal_le_local_holder
    (f : ParabolicSpace → ℝ) {D E : Set ParabolicSpace} {a L : ℝ}
    (hED : E ⊆ D) (hL1 : L ≤ 1)
    (hb : BddAbove (localSourceHolderValues f a D L))
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, Local.pdist x y ≤ L) :
    (scalarHolderSeminorm f E a).toReal ≤ localSourceHolder f a D L := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (scalarHolderSeminorm_le_local_holder_on_diameter f hED hL1 hb hdiam)
  rwa [ENNReal.toReal_ofReal (localSourceHolder_nonneg hb)] at hh

/-- Domain restriction for the actual ordinary scalar supremum. -/
theorem localScalarSup_mono_domain (f : ParabolicSpace → ℝ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) : localScalarSup f D ≤ localScalarSup f E := by
  simp only [localScalarSup, iSup_le_iff]
  intro x hx
  exact le_iSup_of_le x (le_iSup_of_le (hDE hx) le_rfl)

end GlobalPhi43.MW20
