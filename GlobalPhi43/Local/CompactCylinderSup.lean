/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.MW20.CylinderSup
public import GlobalPhi43.MW20.RadiusMaximumStep

/-! Cylinder mass estimates need continuity only on the closed unit cylinder.
This is the carrier available from the local-data smoothness hypothesis;
behavior outside that cylinder is unrestricted. -/
public section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20

theorem sourceSup_bddAbove_on {v : ParabolicSpace → ℝ}
    (hv : ContinuousOn v sourceClosedCylinder) {R : ℝ} (hR : 0 ≤ R) :
    BddAbove ((fun z => |v z|) '' sourceCylinder R) := by
  have hb : BddAbove ((fun z => |v z|) '' sourceClosedCylinder) :=
    (isCompact_Icc.image_of_continuousOn hv.abs).bddAbove
  exact hb.mono (image_mono (sourceCylinder_subset_closed hR))

theorem sourceSup_nonneg_on {v : ParabolicSpace → ℝ}
    (hv : ContinuousOn v sourceClosedCylinder) {R : ℝ}
    (hR : R ∈ Icc (0 : ℝ) (1 / 2)) : 0 ≤ sourceSup v R := by
  obtain ⟨z, hz⟩ := sourceCylinder_nonempty hR
  exact (abs_nonneg (v z)).trans
    (le_csSup (sourceSup_bddAbove_on hv hR.1) ⟨z, hz, rfl⟩)

theorem sourceSup_antitone_on {v : ParabolicSpace → ℝ}
    (hv : ContinuousOn v sourceClosedCylinder) :
    AntitoneOn (sourceSup v) (Icc (0 : ℝ) (1 / 2)) := by
  intro r hr s hs hrs
  exact csSup_le_csSup (sourceSup_bddAbove_on hv hr.1)
    ((sourceCylinder_nonempty hs).image _) (image_mono (sourceCylinder_antitone hr.1 hrs))

theorem abs_le_sourceSup_on {v : ParabolicSpace → ℝ}
    (hv : ContinuousOn v sourceClosedCylinder) {R : ℝ} (hR : 0 ≤ R)
    {z : ParabolicSpace} (hz : z ∈ sourceCylinder R) : |v z| ≤ sourceSup v R :=
  le_csSup (sourceSup_bddAbove_on hv hR) ⟨z, hz, rfl⟩

/-- The general radius engine on the actual local carrier. The stopping and
interior-row hypotheses concern the algorithm, not extra smoothness of v. -/
theorem source_radius_estimate_on (v : ParabolicSpace → ℝ)
    (hv : ContinuousOn v sourceClosedCylinder) (Good : ℝ → Prop) {C A : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hmax : ∀ r ∈ Icc (0 : ℝ) (1 / 2), Good r → 0 < sourceSup v r →
      ∀ R, 2 / sourceSup v r ≤ R → r + R < 1 / 2 →
        sourceSup v (r + R) ≤ max (C / (R - 1 / sourceSup v r)) (sourceSup v r / 2))
    (hfail : ∀ r ∈ Icc (0 : ℝ) (1 / 2), ¬ Good r → sourceSup v r ≤ A) :
    ∀ R ∈ Ioc (0 : ℝ) (1 / 2), sourceSup v R ≤ max (8 * C / R) A := by
  exact radiusSequence_estimate_of_maximum (sourceSup v) Good hC (by norm_num) hA
    (fun _ hR => sourceSup_nonneg_on hv hR) (sourceSup_antitone_on hv) hmax hfail

end GlobalPhi43.Local
