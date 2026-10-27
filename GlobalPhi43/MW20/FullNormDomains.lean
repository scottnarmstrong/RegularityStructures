module

public import GlobalPhi43.MW20.ScalarTestingDomains
public import GlobalPhi43.MW20.AffineSeminorm

/-! Positive norm restriction at arbitrary scalar cutoffs and full affine radii. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- Restriction of the actual full affine sup-inf-sup norm, including
infinite values and without a chosen optimal coefficient. -/
theorem localAffineSeminorm_mono_domain
    (U : ParabolicSpace × ParabolicSpace → ℝ) {D E : Set ParabolicSpace}
    (hDE : D ⊆ E) (γ : ℝ) : localAffineSeminorm U D γ ≤ localAffineSeminorm U E γ := by
  simp only [localAffineSeminorm, iSup_le_iff]
  intro x hx
  apply le_iSup_of_le x
  apply le_iSup_of_le (hDE hx)
  apply iInf_mono
  intro ν
  simp only [affineRemainderSeminorm, iSup_le_iff]
  intro y hy hne
  exact le_iSup_of_le y (le_iSup_of_le (hDE hy) (le_iSup_of_le hne le_rfl))

/-- Every local scalar quotient on a testing domain belongs to the actual
source quotient supremum. No artificial cutoff upper bound is required. -/
theorem scalarHolderSeminorm_le_local_holder_any_cutoff
    (f : ParabolicSpace → ℝ) {D E : Set ParabolicSpace} {a L : ℝ}
    (hED : E ⊆ D) (hb : BddAbove (localSourceHolderValues f a D L))
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, Local.pdist x y ≤ L) :
    scalarHolderSeminorm f E a ≤ ENNReal.ofReal (localSourceHolder f a D L) := by
  simp only [scalarHolderSeminorm, iSup_le_iff]
  intro x hx y hy hne
  apply ENNReal.ofReal_le_ofReal
  exact le_csSup hb (Or.inr ⟨x, hED hx, y, hED hy,
    pdist_pos_of_ne hne, hdiam x hx y hy, rfl⟩)

/-- The real value of the actual extended scalar norm obeys the same bound. -/
theorem scalarHolderSeminorm_toReal_le_local_holder_any_cutoff
    (f : ParabolicSpace → ℝ) {D E : Set ParabolicSpace} {a L : ℝ}
    (hED : E ⊆ D) (hb : BddAbove (localSourceHolderValues f a D L))
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, Local.pdist x y ≤ L) :
    (scalarHolderSeminorm f E a).toReal ≤ localSourceHolder f a D L := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (scalarHolderSeminorm_le_local_holder_any_cutoff f hED hb hdiam)
  rwa [ENNReal.toReal_ofReal (localSourceHolder_nonneg hb)] at hh

end GlobalPhi43.MW20
