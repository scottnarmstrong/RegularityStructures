module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-!
# The actual cylinder suprema used in MW20 §4.6

`P_R = (R²,1) × (-1+R,1-R)³`, with no inset at the terminal time.
For a continuous field the supremum of its absolute value is finite,
nonnegative and nonincreasing for `0 ≤ R ≤ 1/2`.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- MW20's open past cylinder inset, including `P_0 = P`. -/
@[expose] def sourceCylinder (R : ℝ) : Set ParabolicSpace :=
  {z | R ^ 2 < z.1 ∧ z.1 < 1 ∧ ∀ i, |z.2 i| < 1 - R}

/-- The closed unit cylinder on which smooth source data are bounded. -/
@[expose] def sourceClosedCylinder : Set ParabolicSpace :=
  Icc ((0 : ℝ), fun _ => (-1 : ℝ)) ((1 : ℝ), fun _ => (1 : ℝ))

/-- The literal supremum norm of a real field on `P_R`. -/
@[expose] noncomputable def sourceSup (v : ParabolicSpace → ℝ) (R : ℝ) : ℝ :=
  sSup ((fun z => |v z|) '' sourceCylinder R)

/-- Insetting the cylinder produces nested sets. -/
theorem sourceCylinder_antitone {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    sourceCylinder s ⊆ sourceCylinder r := by
  intro z hz
  refine ⟨?_, hz.2.1, ?_⟩
  · have hs : 0 ≤ s := hr.trans hrs
    nlinarith [hz.1]
  · intro i
    exact (hz.2.2 i).trans_le (by linarith)

/-- All nonnegative insets lie in the same compact cylinder. -/
theorem sourceCylinder_subset_closed {R : ℝ} (hR : 0 ≤ R) :
    sourceCylinder R ⊆ sourceClosedCylinder := by
  intro z hz
  change (0 ≤ z.1 ∧ (fun _ => (-1 : ℝ)) ≤ z.2) ∧
    (z.1 ≤ 1 ∧ z.2 ≤ fun _ => (1 : ℝ))
  refine ⟨⟨(sq_nonneg R).trans hz.1.le, ?_⟩, ⟨hz.2.1.le, ?_⟩⟩
  · intro i
    have hi := (abs_lt.mp (hz.2.2 i)).1
    linarith
  · intro i
    have hi := (abs_lt.mp (hz.2.2 i)).2
    linarith

/-- The source iteration uses only nonempty insets. -/
theorem sourceCylinder_nonempty {R : ℝ} (hR : R ∈ Icc (0 : ℝ) (1 / 2)) :
    (sourceCylinder R).Nonempty := by
  refine ⟨((1 / 2 : ℝ), 0), ?_⟩
  change R ^ 2 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧ ∀ i : Fin 3, |(0 : ℝ)| < 1 - R
  refine ⟨by nlinarith [hR.1, hR.2], by norm_num, ?_⟩
  intro i
  rw [abs_zero]
  linarith [hR.2]

/-- The absolute values on every inset are bounded by compactness of the closed cylinder. -/
theorem sourceSup_bddAbove {v : ParabolicSpace → ℝ} (hv : Continuous v)
    {R : ℝ} (hR : 0 ≤ R) : BddAbove ((fun z => |v z|) '' sourceCylinder R) := by
  have hb : BddAbove ((fun z => |v z|) '' sourceClosedCylinder) :=
    (isCompact_Icc.image hv.abs).bddAbove
  exact hb.mono (image_mono (sourceCylinder_subset_closed hR))

/-- The actual source supremum is nonnegative. -/
theorem sourceSup_nonneg {v : ParabolicSpace → ℝ} (hv : Continuous v)
    {R : ℝ} (hR : R ∈ Icc (0 : ℝ) (1 / 2)) : 0 ≤ sourceSup v R := by
  obtain ⟨z, hz⟩ := sourceCylinder_nonempty hR
  exact (abs_nonneg (v z)).trans
    (le_csSup (sourceSup_bddAbove hv hR.1) ⟨z, hz, rfl⟩)

/-- Restriction to nested cylinders decreases the literal supremum norm. -/
theorem sourceSup_antitone {v : ParabolicSpace → ℝ} (hv : Continuous v) :
    AntitoneOn (sourceSup v) (Icc (0 : ℝ) (1 / 2)) := by
  intro r hr s hs hrs
  exact csSup_le_csSup (sourceSup_bddAbove hv hr.1)
    ((sourceCylinder_nonempty hs).image _) (image_mono (sourceCylinder_antitone hr.1 hrs))

/-- The cylinder supremum controls every evaluation in that cylinder. -/
theorem abs_le_sourceSup {v : ParabolicSpace → ℝ} (hv : Continuous v)
    {R : ℝ} (hR : 0 ≤ R) {z : ParabolicSpace} (hz : z ∈ sourceCylinder R) :
    |v z| ≤ sourceSup v R :=
  le_csSup (sourceSup_bddAbove hv hR) ⟨z, hz, rfl⟩

end GlobalPhi43.MW20
