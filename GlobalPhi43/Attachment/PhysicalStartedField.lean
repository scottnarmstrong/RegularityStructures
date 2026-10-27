module

public import GlobalPhi43.Attachment.StartedClassicalPDE
public import GlobalPhi43.Local.HeatOperatorTransport

/-! Actual restarted solution in physical coordinates, with local smoothness only. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ContDiff

namespace GlobalPhi43.Attachment

/-- The actual selected restart solution at physical time z.time>s. -/
@[expose] def physicalStartedField {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) : ParabolicSpace → ℝ :=
  Local.parabolicPullback 1 (startedClassicalField a s q hq) (-s, 0) 1

private theorem physical_relative_map (s : ℝ) (z : ParabolicSpace) :
    Local.parabolicMap (-s, 0) 1 z = (z.1-s, z.2) := by
  apply Prod.ext <;> simp [Local.parabolicMap, parabolicDilate, sub_eq_add_neg, add_comm]

/-- Smoothness only after the actual physical start. -/
theorem physicalStartedField_smooth {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) :
    ContDiffOn ℝ ∞ (physicalStartedField a s q hq) {z | s < z.1} := by
  apply (Local.parabolicPullback_contDiffOn 1 _ (-s, 0) 1
    (startedClassicalField_smooth a s q hq)).mono
  intro z hz
  change 0 < (Local.parabolicMap (-s, 0) 1 z).1
  rw [physical_relative_map]
  exact sub_pos.mpr hz

/-- The original forcing and EXACT drift appear in the physical-coordinate PDE.
The shift cancels; no PDE or bound is an input. -/
theorem physicalStartedField_pde {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q)
    (z : ParabolicSpace) (hz : s < z.1) :
    heatOperator (physicalStartedField a s q hq) z =
      -(physicalStartedField a s q hq z)^3 + a.forcing (spaceTimeProj z) +
        (3*a.constants.1-9*a.constants.2)*physicalStartedField a s q hq z := by
  have hp : 0 < (Local.parabolicMap (-s, 0) 1 z).1 := by
    rw [physical_relative_map]
    exact sub_pos.mpr hz
  have hh := Local.heatOperator_parabolicPullback 1 (startedClassicalField a s q hq)
    (-s, 0) 1 (O := {w | 0 < w.1}) (isOpen_lt continuous_const continuous_fst)
    (startedClassicalField_smooth a s q hq) z hp
  rw [startedClassicalField_pde a s q hq _ hp] at hh
  simpa only [physicalStartedField, Local.parabolicPullback, one_mul, one_pow,
    physical_relative_map, shiftForcing, spaceTimeProj, sub_add_cancel] using hh

end GlobalPhi43.Attachment
