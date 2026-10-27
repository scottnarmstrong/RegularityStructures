/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic

/-! MW20's max parabolic distance and the cylinder interiors used by the
radius-local Schauder estimate. The space-time carrier is reused from the base.
The interior of P_r at depth d has lower time r²+d², not (r+d)². -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set

/-- MW20's distance, distinct from the base's equivalent sum convention. -/
def pdist (x y : ParabolicSpace) : ℝ :=
  max (Real.sqrt |x.1 - y.1|) ‖x.2 - y.2‖

/-- The open past ball in the exact MW20 convention. -/
def pastBall (x : ParabolicSpace) (L : ℝ) : Set ParabolicSpace :=
  {y | pdist x y < L ∧ y.1 < x.1}

/-- The d-interior of D=P_r. No terminal-time inset is imposed. -/
def cylinderInterior (r d : ℝ) : Set ParabolicSpace :=
  {x | r ^ 2 + d ^ 2 < x.1 ∧ x.1 < 1 ∧
    ∀ i : Fin 3, -1 + r + d < x.2 i ∧ x.2 i < 1 - r - d}

theorem pdist_nonneg (x y : ParabolicSpace) : 0 ≤ pdist x y :=
  (Real.sqrt_nonneg _).trans (le_max_left _ _)

theorem pdist_symm (x y : ParabolicSpace) : pdist x y = pdist y x := by
  simp only [pdist, abs_sub_comm, norm_sub_rev]

theorem pdist_triangle (x y z : ParabolicSpace) :
    pdist x z ≤ pdist x y + pdist y z := by
  apply max_le
  · calc
      Real.sqrt |x.1 - z.1| ≤
          Real.sqrt |x.1 - y.1| + Real.sqrt |y.1 - z.1| := by
        convert sqrt_abs_add_le (x.1 - y.1) (y.1 - z.1) using 1; ring_nf
      _ ≤ pdist x y + pdist y z :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      ‖x.2 - z.2‖ ≤ ‖x.2 - y.2‖ + ‖y.2 - z.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ pdist x y + pdist y z :=
        add_le_add (le_max_right _ _) (le_max_right _ _)

/-- Cylinder interiors are nested in their depth parameter. -/
theorem cylinderInterior_mono {r s d : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) :
    cylinderInterior r d ⊆ cylinderInterior r s := by
  intro x hx
  obtain ⟨ht, ht₁, hspace⟩ := hx
  refine ⟨?_, ht₁, fun i => ?_⟩
  · have : s ^ 2 ≤ d ^ 2 := by nlinarith
    linarith
  · obtain ⟨hl, hu⟩ := hspace i
    constructor <;> linarith

/-- A past ball of radius L loses at most L of the available interior depth. -/
theorem pastBall_subset_interior {r d s L : ℝ} {x : ParabolicSpace}
    (hs : 0 ≤ s) (hL : 0 ≤ L) (hbudget : s + L ≤ d)
    (hx : x ∈ cylinderInterior r d) :
    pastBall x L ⊆ cylinderInterior r s := by
  intro y hy
  obtain ⟨ht, ht₁, hspace⟩ := hx
  obtain ⟨hxy, hypast⟩ := hy
  have htime : |x.1 - y.1| < L ^ 2 :=
    (Real.sqrt_lt (abs_nonneg _) hL).mp ((le_max_left _ _).trans_lt hxy)
  have hnorm : ‖x.2 - y.2‖ < L := (le_max_right _ _).trans_lt hxy
  have hdepth : s ^ 2 + L ^ 2 ≤ d ^ 2 := by nlinarith
  refine ⟨?_, hypast.trans ht₁, fun i => ?_⟩
  · have habs := le_abs_self (x.1 - y.1)
    linarith
  · have hcoord : |x.2 i - y.2 i| < L := by
      have hi := norm_le_pi_norm (x.2 - y.2) i
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi.trans_lt hnorm
    have hi := abs_lt.mp hcoord
    obtain ⟨hl, hu⟩ := hspace i
    constructor <;> linarith [hi.1, hi.2]

end GlobalPhi43.Local
