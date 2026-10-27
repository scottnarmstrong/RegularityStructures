module

public import GlobalPhi43.Flow.SmoothSolutions
public import GlobalPhi43.MW20.Setting.HeatOperator

/-! The heat operator applied to the actual classical periodic lift.
Smoothness is used only at positive physical times. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ContDiff

namespace GlobalPhi43.Attachment

private theorem classical_lift_smoothAt {b : ℝ} {f : SpaceTime → ℝ}
    {q : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution b f q u) {z : ParabolicSpace} (hz : 0 < z.1) :
    ContDiffAt ℝ ∞ (fun w : ParabolicSpace => u w.1 (torusProj w.2)) z :=
  hu.contDiffOn.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)

private theorem classical_lift_space_deriv {b : ℝ} {f : SpaceTime → ℝ}
    {q : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution b f q u) {t : ℝ} (ht : 0 < t)
    (y : Fin 3 → ℝ) (i : Fin 3) (r : ℝ) :
    deriv (fun a => u t (torusProj (Function.update y i a))) r =
      fderiv ℝ (fun w : ParabolicSpace => u w.1 (torusProj w.2))
        (t, Function.update y i r) (0, Pi.single i 1) := by
  have hd := (classical_lift_smoothAt hu (z := (t, Function.update y i r)) ht).differentiableAt
    (by simp)
  have hline := (hasDerivAt_const r t).prodMk (hasDerivAt_update y i r)
  exact (hd.hasFDerivAt.comp_hasDerivAt r hline).deriv

/-- The classical equation in terms of the Fréchet heat operator. -/
theorem classical_heatOperator {b : ℝ} {f : SpaceTime → ℝ}
    {q : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution b f q u) (z : ParabolicSpace) (hz : 0 < z.1) :
    heatOperator (fun w : ParabolicSpace => u w.1 (torusProj w.2)) z =
      -u z.1 (torusProj z.2)^3 + f (spaceTimeProj z) + b*u z.1 (torusProj z.2) := by
  let U : ParabolicSpace → ℝ := fun w => u w.1 (torusProj w.2)
  have hU : ContDiffAt ℝ ∞ U z := classical_lift_smoothAt hu hz
  have hd := hU.differentiableAt (by simp)
  have ht := (hd.hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv
  have hsecond (i : Fin 3) :
      deriv (deriv (fun a => u z.1 (torusProj (Function.update z.2 i a)))) (z.2 i) =
        fderiv ℝ (fun w => fderiv ℝ U w (0, Pi.single i 1)) z (0, Pi.single i 1) := by
    have he : deriv (fun a => u z.1 (torusProj (Function.update z.2 i a))) =
        fun a => fderiv ℝ U (z.1, Function.update z.2 i a) (0, Pi.single i 1) := by
      funext a
      exact classical_lift_space_deriv hu hz z.2 i a
    rw [he]
    have hf : DifferentiableAt ℝ (fun w => fderiv ℝ U w (0, Pi.single i 1)) z :=
      ((hU.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
        (by simp)
    have hline := (hasDerivAt_const (z.2 i) z.1).prodMk
      (hasDerivAt_update z.2 i (z.2 i))
    have hf' : DifferentiableAt ℝ (fun w => fderiv ℝ U w (0, Pi.single i 1))
        (z.1, Function.update z.2 i (z.2 i)) := by simpa using hf
    have hc := hf'.hasFDerivAt.comp_hasDerivAt (z.2 i) hline
    simpa only [Function.comp_def, Function.update_eq_self, Prod.mk.eta] using hc.deriv
  have hp := hu.equation z.1 hz z.2
  rw [show deriv (fun s => u s (torusProj z.2)) z.1 =
    fderiv ℝ U z (1, 0) from ht] at hp
  simp_rw [hsecond] at hp
  change fderiv ℝ U z (1, 0) -
    ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ U w (0, Pi.single i 1)) z
      (0, Pi.single i 1) = _
  change _ = -U z^3 + f (z.1, torusProj z.2) + b*U z
  linarith only [hp]

end GlobalPhi43.Attachment
