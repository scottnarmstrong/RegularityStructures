module

public import GlobalPhi43.Attachment.ProbeJTests
public import GlobalPhi43.Attachment.ProbeFoldIntegral

/-! The literal source compact model window and periodicity of the actual J.
The auxiliary continuity bound here is used only for integrability, never as
an input or constant in the model probe estimate. -/

@[expose] public noncomputable section

open RegularityStructures RegularityStructures.Phi43 MeasureTheory Set

namespace GlobalPhi43.Attachment

def probeModelWindow (s : ℝ) : Set ParabolicSpace :=
  Icc s (s+1) ×ˢ Icc (fun _ : Fin 3 => (-1 : ℝ)) (fun _ => (2 : ℝ))

theorem probeModelWindow_compact (s : ℝ) : IsCompact (probeModelWindow s) :=
  isCompact_Icc.prod isCompact_Icc

theorem probe_lift_integer_periodic (g : SpaceTime → ℝ) (m : Fin 3 → ℤ)
    (w : ParabolicSpace) : g (spaceTimeProj (w+probeIntegerShift m)) = g (spaceTimeProj w) := by
  have he : spaceTimeProj (w+probeIntegerShift m) = spaceTimeProj w := by
    apply Prod.ext
    · simp [spaceTimeProj, probeIntegerShift]
    · funext i
      simp [spaceTimeProj, probeIntegerShift, probeIntegerVector, torusProj]
  rw [he]

theorem probeJ_window_bound {N : ℕ} {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (s : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ParabolicSpace, w.1 ∈ Icc s (s+1) →
      |treeJ N f (spaceTimeProj w)| ≤ M := by
  have hc : IsCompact (Icc s (s+1) ×ˢ (univ : Set Torus3)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn (continuous_treeJ hf).continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro w hw
  exact (hM (spaceTimeProj w) ⟨hw, mem_univ _⟩).trans (le_max_left _ _)

end GlobalPhi43.Attachment
