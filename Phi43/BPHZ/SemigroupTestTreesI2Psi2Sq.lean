/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesKernelData
public import Phi43.BPHZ.SemigroupTestTreesCoupled

/-!
# The square term of the chaos-`4` part of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

`i2Psi2_sq_term_global`: with `A_y = i2Psi2Increment K x y`,
`|∫∫ A_y(w) A_{y'}(v) Q(w - v)²| ≤ C B⁴ D^(1/4) (80/(7/4) + 2 (|y.1 - x.1| + 1))`
whenever `D` bounds `s(w - v)` on the slabs of `A_y`, `A_{y'}`.  The proof dominates the
integrand by the coupled majorant of `coupled_sum_integral` with `α = β = 3`, `k = 2`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem ae_abs_i2Psi2Increment_le {K Q : SpaceTime → ℝ} {B : ℝ} (h : SingularKernelData K Q B)
    (x y : SpaceTime) : ∀ᵐ w : SpaceTime ∂volume, |i2Psi2Increment K x y w| ≤
      B * Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ |y.1 - x.1| + 1}
        (fun w => singularPow 3 y w + singularPow 3 x w) w := by
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x] with w a b
  refine (abs_i2Psi2Increment_le_slab h a b).trans (le_of_eq ?_)
  by_cases hw : w ∈ {w : SpaceTime | |w.1 - x.1| ≤ |y.1 - x.1| + 1}
  · simp only [Set.indicator_of_mem hw]
  · simp only [Set.indicator_of_notMem hw, mul_zero]

/-- Products of three bounded factors. -/
theorem abs_mul_mul_le {a a' q M1 M2 P : ℝ} (ha : |a| ≤ M1) (ha' : |a'| ≤ M2) (hq : |q| ≤ P) :
    |a * a' * q| ≤ M1 * M2 * P := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul ha ha' (abs_nonneg _) ((abs_nonneg _).trans ha)) hq (abs_nonneg _)
    (mul_nonneg ((abs_nonneg _).trans ha) ((abs_nonneg _).trans ha'))

/-- The square term of chaos `4`. -/
theorem i2Psi2_sq_term_global :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y y' : SpaceTime) {D : ℝ}, 0 ≤ D →
      (∀ w v : SpaceTime, |w.1 - x.1| ≤ |y.1 - x.1| + 1 → |v.1 - x.1| ≤ |y'.1 - x.1| + 1 →
        torusParabolicSize (w - v) ≤ D) →
      Integrable (Function.uncurry fun w v =>
          i2Psi2Increment K x y w * i2Psi2Increment K x y' v * Q (w - v) ^ 2)
        (volume.prod volume) ∧
      |∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v * Q (w - v) ^ 2| ≤
        C * B ^ 4 * D ^ (1 / 4 : ℝ) * (80 / (5 - (3 + 1 / 4)) + 2 * (|y.1 - x.1| + 1)) := by
  obtain ⟨C0, hC0, h0⟩ := coupled_sum_integral (α := 3) (β := 3) (k := 2) (δ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C0 * 4, by positivity, ?_⟩
  intro K Q B h x y y' D hD0 hD
  have hB := h.nonneg
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime => i2Psi2Increment K x y p.1 *
      i2Psi2Increment K x y' p.2 * Q (p.1 - p.2) ^ 2) := by
    have := h.measurable_increment x y
    have := h.measurable_increment x y'
    have := h.measurable_Q
    fun_prop
  have e1 : (fun w => ∑ i, (![1, 1, 0] : Fin 3 → ℝ) i * singularPow 3 (![y, x, x] i) w) =
      fun w => singularPow 3 y w + singularPow 3 x w := by
    funext w; simp [Fin.sum_univ_three]
  have e2 : (fun w => ∑ i, (![1, 1, 0] : Fin 3 → ℝ) i * singularPow 3 (![y', x, x] i) w) =
      fun w => singularPow 3 y' w + singularPow 3 x w := by
    funext w; simp [Fin.sum_univ_three]
  have e3 : (∑ i, (![1, 1, 0] : Fin 3 → ℝ) i) = 2 := by
    simp [Fin.sum_univ_three]; norm_num
  have key := h0 (F := fun w v => i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
      Q (w - v) ^ 2) (Λ := B ^ 4) (τ := x.1) (τ' := x.1) (T := |y.1 - x.1| + 1)
    (T' := |y'.1 - x.1| + 1) (D := D) (c := ![1, 1, 0]) (c' := ![1, 1, 0])
    (q := ![y, x, x]) (q' := ![y', x, x]) (by positivity) (by positivity) (by positivity) hD0
    (by intro i; fin_cases i <;> simp) (by intro j; fin_cases j <;> simp)
    hmeas.aestronglyMeasurable hD ?_
  · refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
    rw [e3]
    ring
  · rw [e1, e2]
    filter_upwards [ae_abs_i2Psi2Increment_le h x y] with w hw
    filter_upwards [ae_abs_i2Psi2Increment_le h x y', ae_torusParabolicSize_sub_pos w] with v hv hpos
    have hq := abs_Q_sq_le_singularPow h.Q_bound hpos
    have hI1 : 0 ≤ Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ |y.1 - x.1| + 1}
        (fun w => singularPow 3 y w + singularPow 3 x w) w :=
      Set.indicator_nonneg (fun w _ => add_nonneg (singularPow_nonneg _ _ _)
        (singularPow_nonneg _ _ _)) w
    have hI2 : 0 ≤ Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ |y'.1 - x.1| + 1}
        (fun w => singularPow 3 y' w + singularPow 3 x w) v :=
      Set.indicator_nonneg (fun w _ => add_nonneg (singularPow_nonneg _ _ _)
        (singularPow_nonneg _ _ _)) v
    have := abs_mul_mul_le (a := i2Psi2Increment K x y w) (a' := i2Psi2Increment K x y' v)
      (q := Q (w - v) ^ 2) hw hv (P := B ^ 2 * singularPow 2 w v) (by
        rw [abs_of_nonneg (sq_nonneg _)]
        have := hq
        rwa [sq_abs] at this)
    refine this.trans (le_of_eq ?_)
    ring

end RegularityStructures

end
