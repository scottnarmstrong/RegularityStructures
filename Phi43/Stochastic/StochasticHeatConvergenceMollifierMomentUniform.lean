/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsLocal

/-!
# Uniform parabolic moments of the periodised mollifier

The support constant and the rescaling-invariant `L¹` norm are independent of the scale.  This
module puts the scale binders after the existential constant, which is the quantifier order needed
when estimating differences of two regularisations.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem integral_abs_periodise_mul_parabolicSize_rpow_le_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∫ w : SpaceTime, |periodise ρ ε w| *
        torusParabolicSize w ^ θ ≤ C * ε ^ θ := by
  obtain ⟨B, hB, hsupport⟩ := periodise_support_parabolic_bound ρ hρ
  let N : ℝ := ∫ y : ParabolicSpace, |ρ y|
  have hN : 0 ≤ N := by
    dsimp [N]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have hweight_meas : AEStronglyMeasurable
      (fun w : SpaceTime => torusParabolicSize w ^ θ) := by
    by_cases hθ0 : θ = 0
    · subst θ
      simpa using
        (measurable_const : Measurable (fun _ : SpaceTime => (1 : ℝ))).aestronglyMeasurable
    · have hm := (measurable_pos_rpow_extension θ).comp measurable_torusParabolicSize
      have hm' : AEStronglyMeasurable
          (fun w : SpaceTime => if 0 < torusParabolicSize w then
            torusParabolicSize w ^ θ else 0) := hm.aestronglyMeasurable
      apply hm'.congr
      filter_upwards [] with w
      by_cases hw : 0 < torusParabolicSize w
      · simp [hw]
      · have hw0 : torusParabolicSize w = 0 :=
          le_antisymm (le_of_not_gt hw) (torusParabolicSize_nonneg w)
        rw [hw0]
        simp [Real.zero_rpow hθ0]
  refine ⟨B ^ θ * N, by positivity, ?_⟩
  intro ε hε hε1
  let D : ℝ := (B * ε) ^ θ
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg (mul_nonneg hB.le hε.le) _
  have hP : Integrable (fun w : SpaceTime => |periodise ρ ε w|) :=
    (integrable_periodise ρ hρ hε).norm
  have hNbound : ∫ w : SpaceTime, |periodise ρ ε w| ≤ N := by
    calc
      ∫ w : SpaceTime, |periodise ρ ε w| ≤ ∫ y : ParabolicSpace, |rescale ρ ε y| :=
        integral_abs_periodise_le ρ hρ hε hε1
      _ = N := by
        dsimp [N]
        exact integral_abs_rescale_eq ρ hε
  have hmajor : Integrable (fun w : SpaceTime => D * |periodise ρ ε w|) :=
    hP.const_mul D
  have hprod_meas : AEStronglyMeasurable (fun w : SpaceTime =>
      |periodise ρ ε w| * torusParabolicSize w ^ θ) :=
    ((measurable_periodise ρ hρ).norm.aestronglyMeasurable.mul hweight_meas)
  have hpoint : ∀ w : SpaceTime,
      |periodise ρ ε w| * torusParabolicSize w ^ θ ≤
        D * |periodise ρ ε w| := by
    intro w
    by_cases hzero : periodise ρ ε w = 0
    · simp [hzero]
    · have hsize := hsupport hε hε1 w hzero
      have hp := Real.rpow_le_rpow (torusParabolicSize_nonneg w) hsize hθ
      simpa [D, mul_comm] using
        mul_le_mul_of_nonneg_right hp (abs_nonneg (periodise ρ ε w))
  have hmoment : Integrable (fun w : SpaceTime =>
      |periodise ρ ε w| * torusParabolicSize w ^ θ) := by
    apply hmajor.mono' hprod_meas
    filter_upwards [] with w
    by_cases hzero : periodise ρ ε w = 0
    · simp [hzero]
    · have hsize := hsupport hε hε1 w hzero
      have hp := Real.rpow_le_rpow (torusParabolicSize_nonneg w) hsize hθ
      simpa [D, mul_comm, abs_of_nonneg (Real.rpow_nonneg
        (torusParabolicSize_nonneg w) _)] using
        (show torusParabolicSize w ^ θ * |periodise ρ ε w| ≤
            (B * ε) ^ θ * |periodise ρ ε w| from
          mul_le_mul_of_nonneg_right hp (abs_nonneg (periodise ρ ε w)))
  calc
    ∫ w : SpaceTime, |periodise ρ ε w| * torusParabolicSize w ^ θ ≤
        D * ∫ w : SpaceTime, |periodise ρ ε w| := by
      calc
        ∫ w : SpaceTime, |periodise ρ ε w| * torusParabolicSize w ^ θ ≤
            ∫ w : SpaceTime, D * |periodise ρ ε w| := integral_mono hmoment hmajor hpoint
        _ = D * ∫ w : SpaceTime, |periodise ρ ε w| := integral_const_mul _ _
    _ ≤ D * N := mul_le_mul_of_nonneg_left hNbound hD
    _ = (B ^ θ * N) * ε ^ θ := by
      dsimp [D]
      rw [Real.mul_rpow hB.le hε.le]
      ring

end RegularityStructures.Phi43

end
