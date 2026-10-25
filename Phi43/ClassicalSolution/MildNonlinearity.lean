/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.Existence

/-!
# The untruncated cubic heat nonlinearity

The nonlinearity `-u³ + c u + f` of the renormalised equation (3.1) of the statement is smooth on its
whole carrier. The scalar `c` includes the renormalisation constants; no cutoff is used.
-/

@[expose] public noncomputable section

open RegularityStructures.PDE

namespace RegularityStructures.Phi43

/-- The nonlinearity `-v³ + c v + f(t,x)` of the renormalised classical equation. -/
def cubicHeatNonlinearity (c : ℝ) {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) :
    C(ℝ × Torus3 × ℝ, ℝ) :=
  ⟨fun p => -p.2.2 ^ 3 + c * p.2.2 + f (p.1, p.2.1),
    (((continuous_snd.comp continuous_snd).pow 3).neg.add
      (continuous_const.mul (continuous_snd.comp continuous_snd))).add
        ((continuous_of_isSmoothOnSpaceTime hf).comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))⟩

theorem cubicHeatNonlinearity_apply (c : ℝ) {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (t : ℝ) (x : Torus3) (v : ℝ) :
    cubicHeatNonlinearity c hf (t, x, v) = -v ^ 3 + c * v + f (t, x) := rfl

open scoped ContDiff in
theorem contDiff_nonlinLift_cubicHeatNonlinearity (c : ℝ) {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) :
    ContDiff ℝ ∞ (nonlinLift (cubicHeatNonlinearity c hf)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) × ℝ =>
    -p.2.2 ^ 3 + c * p.2.2 + f (p.1, torusProj p.2.1))
  exact (((contDiff_snd.comp contDiff_snd).pow 3).neg.add
    (contDiff_const.mul (contDiff_snd.comp contDiff_snd))).add
      (hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)))

end RegularityStructures.Phi43

end
