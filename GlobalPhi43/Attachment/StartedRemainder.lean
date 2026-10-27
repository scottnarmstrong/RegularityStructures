module

public import GlobalPhi43.Attachment.StartedClassicalPDE
public import GlobalPhi43.Attachment.SmoothNoiseSlices

/-! The actual u-minus-J path used by the conditional cover application. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Attachment

/-- Restarted classical solution minus the original noise primitive at physical time s+t. -/
@[expose] def startedRemainder {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) (t : ℝ) : C(Torus3, ℝ) :=
  Flow.smoothSolution (3*a.constants.1-9*a.constants.2)
    (shiftForcing s a.forcing) (a.shiftSmooth s) q hq t -
      smoothNoiseJ N ⟨a.forcing, Flow.smooth_of_moderateLift a.moderate⟩ (s+t)

/-- Positive-time continuity, without a solution bound or bounded-defect hypothesis. -/
theorem startedRemainder_continuousOn {N : ℕ} {κ : Kappa} (a : Flow.LiftData N κ)
    (s : ℝ) (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) :
    ContinuousOn (fun z : ParabolicSpace => startedRemainder a s q hq z.1 (torusProj z.2))
      {z | 0 < z.1} := by
  have hu := (startedClassicalField_smooth a s q hq).continuousOn
  have hJ : Continuous (fun z : ParabolicSpace =>
      treeJ N a.forcing (s+z.1, torusProj z.2)) :=
    (continuous_treeJ (Flow.smooth_of_moderateLift a.moderate)).comp
      ((continuous_const.add continuous_fst).prodMk
        (PDE.continuous_torusProj.comp continuous_snd))
  exact hu.sub hJ.continuousOn

end GlobalPhi43.Attachment
