/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusBasic

/-!
# Support of the torus parabolic test function in the parabolic size

For `φ` in the test-function class, `lam > 0` and a base point `z`, the test function
`torusParabolicTestIoc φ lam z` is bounded by `lam⁻⁵` times the indicator of a measurable set `K`
of volume at most `16 lam⁵` on which `s(w - z) ≤ 3 lam`, where `s = torusParabolicSize`.

**Cell boundary.**  The test function is centred at the `(0, 1]`-representative of `z.2` and lives in
the box `torusBoxIoc`, which may straddle the boundary of the representative cell `(0, 1]³`.  The
torus parabolic size `s(w - z)` is computed from the centred representative of `w.2 - z.2` and is
bounded by the Euclidean norm of the difference of any two lifts
(`abs_torusCenteredRep_le_abs_of_torusProj`), in particular of the two `(0, 1]`-representatives.
Thus the bound `s(w - z) ≤ 3 lam` holds on the whole support, whether or not the box wraps around.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- The centred representative is shorter than any lift. -/
theorem abs_torusCenteredRep_le_abs_of_torusProj {x : Torus3} {u : Fin 3 → ℝ}
    (h : torusProj u = x) (i : Fin 3) : |torusCenteredRep x i| ≤ |u i| := by
  have hc := torusCenteredRep_mem_Icc x i
  have e1 : ((torusCenteredRep x i : ℝ) : UnitAddCircle) = x i :=
    congrFun (torusProj_torusCenteredRep x) i
  have e2 : ((u i : ℝ) : UnitAddCircle) = x i := congrFun h i
  have hsub : (((torusCenteredRep x i - u i : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, e1, e2, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 hsub
  have hn' : (n : ℝ) = torusCenteredRep x i - u i := by simpa using hn
  by_cases hu : 1 / 2 ≤ |u i|
  · exact (abs_le.2 hc).trans hu
  · have hu' := abs_lt.1 (not_le.1 hu)
    have h1 : (n : ℝ) < 1 := by linarith [hc.2]
    have h2 : (-1 : ℝ) < n := by linarith [hc.1]
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : -1 < n := by exact_mod_cast h2
    have hn0 : n = 0 := by omega
    rw [hn0] at hn'
    push_cast at hn'
    rw [show torusCenteredRep x i = u i by linarith]

end RegularityStructures

end
