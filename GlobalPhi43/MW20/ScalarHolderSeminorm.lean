module

public import GlobalPhi43.MW20.AffineSeminorm

/-! The actual local scalar Holder seminorm (MW20 (2.4)) and its pointwise
increment extraction. Extended values retain unbounded seminorms faithfully. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal

/-- The source's two-sided scalar Holder seminorm on a specified domain. -/
@[expose] noncomputable def scalarHolderSeminorm
    (f : ParabolicSpace → ℝ) (D : Set ParabolicSpace) (α : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ y ∈ D, ⨆ (_ : y ≠ x), ENNReal.ofReal (|f y - f x| / pdist x y ^ α)

/-- Extract a true increment bound from the actual positive source norm.
Coincident points are included, without a diagonal-continuity assumption. -/
theorem scalarHolderSeminorm_increment_bound
    (f : ParabolicSpace → ℝ) (D : Set ParabolicSpace) (α : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hnorm : scalarHolderSeminorm f D α ≤ ENNReal.ofReal C)
    {x y : ParabolicSpace} (hx : x ∈ D) (hy : y ∈ D) :
    |f y - f x| ≤ C * pdist x y ^ α := by
  by_cases he : y = x
  · subst y
    simpa only [sub_self, abs_zero] using mul_nonneg hC (Real.rpow_nonneg (pdist_nonneg x x) α)
  · have hh : ∀ x ∈ D, ∀ y ∈ D, ∀ (_ : y ≠ x),
        ENNReal.ofReal (|f y - f x| / pdist x y ^ α) ≤ ENNReal.ofReal C := by
      simpa only [scalarHolderSeminorm, iSup_le_iff] using hnorm
    have hb := (ENNReal.ofReal_le_ofReal_iff hC).mp (hh x hx y hy he)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne he) _)).mp hb

end GlobalPhi43.MW20
