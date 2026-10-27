module

public import GlobalPhi43.Attachment.ClassicalHeatOperator
public import GlobalPhi43.Flow.DyadicLiftData
public import GlobalPhi43.Attachment.CoverCylinder

/-! The actual chosen classical solution, shifted forcing and reference counterterms. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ContDiff

namespace GlobalPhi43.Attachment

/-- Actual selected solution field in the relative coordinates of a real restart.
The constants are precisely those of LiftData, with no replacement drift. -/
@[expose] def startedClassicalField {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) : ParabolicSpace → ℝ :=
  fun z => Flow.smoothSolution (3*a.constants.1-9*a.constants.2)
    (shiftForcing s a.forcing) (a.shiftSmooth s) q hq z.1 (torusProj z.2)

/-- Smoothness is restricted to the actual positive relative-time domain. -/
theorem startedClassicalField_smooth {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) :
    ContDiffOn ℝ ∞ (startedClassicalField a s q hq) {z | 0 < z.1} := by
  apply (Flow.smoothSolution_spec _ _ (a.shiftSmooth s) q hq).contDiffOn.mono
  intro z hz
  exact ⟨hz, Set.mem_univ _⟩

/-- The evolution equation for the chosen solution at every real starting time
and every smooth initial datum, without a norm bound or additional solution. -/
theorem startedClassicalField_pde {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q)
    (z : ParabolicSpace) (hz : 0 < z.1) :
    heatOperator (startedClassicalField a s q hq) z =
      -(startedClassicalField a s q hq z)^3 +
        shiftForcing s a.forcing (spaceTimeProj z) +
          (3*a.constants.1-9*a.constants.2)*startedClassicalField a s q hq z :=
  classical_heatOperator (Flow.smoothSolution_spec _ _ (a.shiftSmooth s) q hq) z hz

end GlobalPhi43.Attachment
