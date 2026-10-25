/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Cross

/-!
# The coupled terms of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

* `i2Psi2_cross_term_global`: `∫∫ A_y(w) A_{y'}(v) Q(w - v) Q(w - y') Q(y - v)`;
* `i2Psi2_chain_term_global`: `∫∫ A_y(w) A_{y'}(v) Q(w - y) Q(v - y') Q(w - v)`.

Both are bounded by `C B⁵ D^(1/4) (80/(3/4) + 2 (|y.1 - x.1| + 1))`, where `D` bounds `s(w - v)` on
the slabs of `A_y`, `A_{y'}`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The cross term of chaos `4`. -/
theorem i2Psi2_cross_term_global :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y y' : SpaceTime) {D : ℝ}, 0 ≤ D →
      (∀ w v : SpaceTime, |w.1 - x.1| ≤ |y.1 - x.1| + 1 → |v.1 - x.1| ≤ |y'.1 - x.1| + 1 →
        torusParabolicSize (w - v) ≤ D) →
      Integrable (Function.uncurry fun w v => i2Psi2Increment K x y w *
          i2Psi2Increment K x y' v * (Q (w - v) * Q (w - y') * Q (y - v)))
        (volume.prod volume) ∧
      |∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
          (Q (w - v) * Q (w - y') * Q (y - v))| ≤
        C * B ^ 5 * D ^ (1 / 4 : ℝ) * (80 / (5 - (4 + 1 / 4)) + 2 * (|y.1 - x.1| + 1)) := by
  obtain ⟨C0, hC0, h0⟩ := coupled_four_four_integral
  refine ⟨C0 * 2 * 16, by positivity, ?_⟩
  intro K Q B h x y y' D hD0 hD
  have hB := h.nonneg
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime => i2Psi2Increment K x y p.1 *
      i2Psi2Increment K x y' p.2 * (Q (p.1 - p.2) * Q (p.1 - y') * Q (y - p.2))) := by
    have := h.measurable_increment x y
    have := h.measurable_increment x y'
    have := h.measurable_Q
    fun_prop
  have key := h0 (F := fun w v => i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
      (Q (w - v) * Q (w - y') * Q (y - v))) (Λ := 2 * B ^ 5) (τ := x.1)
    (T := |y.1 - x.1| + 1) (T' := |y'.1 - x.1| + 1) (D := D) (p₁ := y) (p₂ := x) (e := y')
    (p₁' := y') (p₂' := x) (e' := y) (by positivity) (by positivity) (by positivity) hD0
    hmeas.aestronglyMeasurable hD ?_
  · refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
    ring
  · filter_upwards [ae_abs_i2Psi2Increment_le h x y, ae_torusParabolicSize_sub_pos y'] with w hw hpw
    filter_upwards [ae_abs_i2Psi2Increment_le h x y', ae_torusParabolicSize_sub_pos w,
      ae_torusParabolicSize_sub_pos y] with v hv hpv hpy
    have q1 := abs_Q_le_singularPow h.Q_bound hpv
    have q2 := abs_Q_flip_le hB h.Q_bound hpw
    have q3 := abs_Q_le_singularPow h.Q_bound hpy
    have hQ : |Q (w - v) * Q (w - y') * Q (y - v)| ≤
        (B * singularPow 1 w v) * (2 * B * singularPow 1 y' w) * (B * singularPow 1 y v) :=
      abs_mul_mul_le q1 q2 q3
    have := abs_mul_mul_le hw hv hQ
    refine this.trans (le_of_eq ?_)
    ring

/-- The chain term of chaos `2`. -/
theorem i2Psi2_chain_term_global :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y y' : SpaceTime) {D : ℝ}, 0 ≤ D →
      (∀ w v : SpaceTime, |w.1 - x.1| ≤ |y.1 - x.1| + 1 → |v.1 - x.1| ≤ |y'.1 - x.1| + 1 →
        torusParabolicSize (w - v) ≤ D) →
      Integrable (Function.uncurry fun w v => i2Psi2Increment K x y w *
          i2Psi2Increment K x y' v * (Q (w - y) * Q (v - y') * Q (w - v)))
        (volume.prod volume) ∧
      |∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
          (Q (w - y) * Q (v - y') * Q (w - v))| ≤
        C * B ^ 5 * D ^ (1 / 4 : ℝ) * (80 / (5 - (4 + 1 / 4)) + 2 * (|y.1 - x.1| + 1)) := by
  obtain ⟨C0, hC0, h0⟩ := coupled_four_four_integral
  refine ⟨C0 * 4 * 16, by positivity, ?_⟩
  intro K Q B h x y y' D hD0 hD
  have hB := h.nonneg
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime => i2Psi2Increment K x y p.1 *
      i2Psi2Increment K x y' p.2 * (Q (p.1 - y) * Q (p.2 - y') * Q (p.1 - p.2))) := by
    have := h.measurable_increment x y
    have := h.measurable_increment x y'
    have := h.measurable_Q
    fun_prop
  have key := h0 (F := fun w v => i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
      (Q (w - y) * Q (v - y') * Q (w - v))) (Λ := 4 * B ^ 5) (τ := x.1)
    (T := |y.1 - x.1| + 1) (T' := |y'.1 - x.1| + 1) (D := D) (p₁ := y) (p₂ := x) (e := y)
    (p₁' := y') (p₂' := x) (e' := y') (by positivity) (by positivity) (by positivity) hD0
    hmeas.aestronglyMeasurable hD ?_
  · refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
    ring
  · filter_upwards [ae_abs_i2Psi2Increment_le h x y, ae_torusParabolicSize_sub_pos y] with w hw hpw
    filter_upwards [ae_abs_i2Psi2Increment_le h x y', ae_torusParabolicSize_sub_pos w,
      ae_torusParabolicSize_sub_pos y'] with v hv hpv hpy
    have q1 := abs_Q_flip_le hB h.Q_bound hpw
    have q2 := abs_Q_flip_le hB h.Q_bound hpy
    have q3 := abs_Q_le_singularPow h.Q_bound hpv
    have hQ : |Q (w - y) * Q (v - y') * Q (w - v)| ≤
        (2 * B * singularPow 1 y w) * (2 * B * singularPow 1 y' v) * (B * singularPow 1 w v) :=
      abs_mul_mul_le q1 q2 q3
    have := abs_mul_mul_le hw hv hQ
    refine this.trans (le_of_eq ?_)
    ring

end RegularityStructures

end
