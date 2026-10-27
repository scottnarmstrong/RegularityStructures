/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.TimeFreeGeometry

/-! The closed boxes needed for derivative bounds remain in the original
source cylinder, with no terminal inset. -/
public section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20

theorem closed_past_box_interior {r d R : ℝ} {x z : ParabolicSpace}
    (hR : 0 ≤ R) (hRd : R ≤ d) (hx : x ∈ cylinderInterior r d)
    (ht : x.1 - R ^ 2 ≤ z.1) (htx : z.1 ≤ x.1) (hs : ‖z.2 - x.2‖ ≤ R) :
    z ∈ cylinderInterior r (d - R) := by
  refine ⟨?_, htx.trans_lt hx.2.1, fun i => ?_⟩
  · have hmul := mul_nonneg hR (sub_nonneg.mpr hRd)
    nlinarith [hx.1]
  · have hi : |z.2 i - x.2 i| ≤ R := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using (norm_le_pi_norm (z.2 - x.2) i).trans hs
    obtain ⟨hl, hu⟩ := hx.2.2 i
    have hb := abs_le.mp hi
    constructor <;> linarith

theorem closed_past_box_mem_source {r d R : ℝ} {x z : ParabolicSpace}
    (hR : 0 ≤ R) (hRd : R ≤ d) (hx : x ∈ cylinderInterior r d)
    (ht : x.1 - R ^ 2 ≤ z.1) (htx : z.1 ≤ x.1) (hs : ‖z.2 - x.2‖ ≤ R) :
    z ∈ sourceCylinder r :=
  cylinderInterior_mem_domain (sub_nonneg.mpr hRd) (closed_past_box_interior hR hRd hx ht htx hs)

end GlobalPhi43.Local
