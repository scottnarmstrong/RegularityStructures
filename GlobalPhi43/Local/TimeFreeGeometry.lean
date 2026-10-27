/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.RadiusGeometry
public import GlobalPhi43.MW20.CylinderSup

/-! Rectangle geometry for all time orders. Domain membership supplies
the upper time bound; no terminal inset is added. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20

/-- The time-free metric neighbourhood used only in the three-point hypothesis. -/
def symmetricBall (x : ParabolicSpace) (L : ℝ) : Set ParabolicSpace :=
  {y | pdist x y < L}

/-- Every nonnegative interior depth stays inside its source cylinder. -/
theorem cylinderInterior_mem_domain {r d : ℝ} {x : ParabolicSpace}
    (hd : 0 ≤ d) (hx : x ∈ cylinderInterior r d) : x ∈ sourceCylinder r := by
  refine ⟨by nlinarith [hx.1, sq_nonneg d], hx.2.1, fun i => ?_⟩
  apply abs_lt.mpr
  obtain ⟨hl, hu⟩ := hx.2.2 i
  constructor <;> linarith

/-- A symmetric displacement loses at most its radius of interior depth,
provided the target point remains in D. In particular its time is below 1. -/
theorem symmetricBall_interior_of_mem_domain {r d s L : ℝ} {x y : ParabolicSpace}
    (hs : 0 ≤ s) (hL : 0 ≤ L) (hbudget : s + L ≤ d)
    (hx : x ∈ cylinderInterior r d) (hyD : y ∈ sourceCylinder r)
    (hxy : y ∈ symmetricBall x L) : y ∈ cylinderInterior r s := by
  obtain ⟨ht, _, hspace⟩ := hx
  have htime : |x.1 - y.1| < L ^ 2 :=
    (Real.sqrt_lt (abs_nonneg _) hL).mp ((le_max_left _ _).trans_lt hxy)
  have hnorm : ‖x.2 - y.2‖ < L := (le_max_right _ _).trans_lt hxy
  have hdepth : s ^ 2 + L ^ 2 ≤ d ^ 2 := by nlinarith
  refine ⟨?_, hyD.2.1, fun i => ?_⟩
  · have habs := le_abs_self (x.1 - y.1)
    linarith
  · have hcoord : |x.2 i - y.2 i| < L := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm (x.2 - y.2) i).trans_lt hnorm
    have hi := abs_lt.mp hcoord
    obtain ⟨hl, hu⟩ := hspace i
    constructor <;> linarith [hi.1, hi.2]

/-- The full local rectangle, including future and equal-time configurations. -/
theorem time_free_three_point_domain {r d : ℝ} {x y z : ParabolicSpace}
    (hd : 0 ≤ d) (hx : x ∈ cylinderInterior r d)
    (hyD : y ∈ sourceCylinder r) (hy : y ∈ symmetricBall x (d / 2))
    (hzD : z ∈ sourceCylinder r) (hz : z ∈ symmetricBall y (d / 4)) :
    x ∈ cylinderInterior r (d / 4) ∧
      y ∈ cylinderInterior r (d / 4) ∧ z ∈ cylinderInterior r (d / 4) := by
  have hyhalf : y ∈ cylinderInterior r (d / 2) :=
    symmetricBall_interior_of_mem_domain (by positivity) (by positivity)
      (by linarith) hx hyD hy
  exact ⟨cylinderInterior_mono (by positivity) (by linarith) hx,
    cylinderInterior_mono (by positivity) (by linarith) hyhalf,
    symmetricBall_interior_of_mem_domain (by positivity) (by positivity)
      (by linarith) hyhalf hzD hz⟩

end GlobalPhi43.Local
