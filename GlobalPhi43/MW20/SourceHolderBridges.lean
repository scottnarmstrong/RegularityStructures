module

public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.RadiusHolderSeminorm

/-!
# Actual positive source norm bridges for the coefficient estimate
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The real source quotient supremum bounds the extended truncated norm.
Finiteness is explicit, so an unbounded real supremum is never used. -/
theorem radiusHolderSeminorm_le_localSourceHolder {v : ParabolicSpace → ℝ}
    {D : Set ParabolicSpace} {α L : ℝ}
    (hb : BddAbove (localSourceHolderValues v α D L)) (hL : L ≤ 1) :
    radiusHolderSeminorm v D α L ≤ ENNReal.ofReal (localSourceHolder v α D L) := by
  simp only [radiusHolderSeminorm, iSup_le_iff]
  intro x hx y hy hcut
  apply ENNReal.ofReal_le_ofReal
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hcut.2) α)).2
    (localSourceHolder_increment hb hx hy hcut.1 hL)

end GlobalPhi43.MW20
