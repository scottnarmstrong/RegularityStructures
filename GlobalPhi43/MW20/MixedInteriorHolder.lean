module

public import GlobalPhi43.MW20.LocalSourceHolder

/-!
# Actual positive seminorms on the mixed-time source interiors D_d
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The exact mixed-time D_d domain lies in P_d, with no replacement of its
lower time r²+d² by (r+d)². -/
theorem mixedInterior_subset_sourceCylinder {r d : ℝ} (hr : 0 ≤ r) :
    Local.cylinderInterior r d ⊆ sourceCylinder d := by
  intro z hz
  refine ⟨by nlinarith [hz.1, sq_nonneg r], hz.2.1, ?_⟩
  intro i
  rw [abs_lt]
  exact ⟨by linarith [(hz.2.2 i).1], by linarith [(hz.2.2 i).2]⟩

/-- A nonempty mixed interior has depth below one. -/
theorem mixedInterior_depth_lt_one {r d : ℝ} (hr : 0 ≤ r)
    {x : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d) : d < 1 := by
  have hl := (hx.2.2 (0 : Fin 3)).1
  have hu := (hx.2.2 (0 : Fin 3)).2
  linarith

/-- The ordinary source C² hypothesis proves finiteness of every positive
local Hölder seminorm on the actual mixed D_d domain. -/
theorem mixedInteriorHolder_bddAbove {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {r d α L : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hα : α ≤ 1) (hL : L ≤ 1) :
    BddAbove (localSourceHolderValues v α (Local.cylinderInterior r d) L) :=
  localSourceHolder_bddAbove hv hd hα hL (mixedInterior_subset_sourceCylinder hr)

end GlobalPhi43.MW20
