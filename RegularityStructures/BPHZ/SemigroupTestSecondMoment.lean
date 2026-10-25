/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.RandomFieldFubini
public import RegularityStructures.Torus.Basic

/-!
# Second moment of a random field tested against an integrable function

Let `Y` be a jointly measurable random field on `ℝ × T³` with uniformly bounded second moments and
covariance `E[Y(u) Y(v)] = Φ(u, v)`, and `g ∈ L¹`.  Then
`E|∫ Y g|² ≤ ∫∫ |g(u)| |g(v)| |Φ(u, v)|` (`secondMoment_le_integral_abs_cov`).

This is the Fubini step of `treePsi_second_moment_le`, for a test function without compact support
and a covariance which is not necessarily translation invariant; the right-hand side is estimated
by `SemigroupTestProfile.integral_double_abs_cov_le` or `SemigroupTestProfile.integral_double_le`.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Second moment against an `L¹` test function.** -/
theorem secondMoment_le_integral_abs_cov [IsProbabilityMeasure P] {Y : Ω → SpaceTime → ℝ}
    (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2)
    (hL2 : ∀ u, MemLp (fun ω => Y ω u) 2 P) {M : ℝ}
    (hM : ∀ u, ∫ ω, Y ω u * Y ω u ∂P ≤ M) {Φ : SpaceTime → SpaceTime → ℝ}
    (hcov : ∀ u v, ∫ ω, Y ω u * Y ω v ∂P = Φ u v) {g : SpaceTime → ℝ} (hg : Integrable g) :
    ∫ ω, |∫ w, Y ω w * g w| ^ 2 ∂P ≤
      ∫ q : SpaceTime × SpaceTime, |g q.1| * |g q.2| * |Φ q.1 q.2| := by
  have hsq : ∀ ω, |∫ w, Y ω w * g w| ^ 2 =
      ∫ q : SpaceTime × SpaceTime, (g q.1 * g q.2) * (Y ω q.1 * Y ω q.2) := by
    intro ω
    have := integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => Y ω w * g w) (fun w => Y ω w * g w)
    rw [sq_abs, sq]
    refine this.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_))
    simp only
    ring
  have hYj : Measurable (fun q : Ω × (SpaceTime × SpaceTime) => Y q.1 q.2.1 * Y q.1 q.2.2) :=
    (hY.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hY.comp (measurable_fst.prodMk measurable_snd.snd))
  have hbound : ∀ q : SpaceTime × SpaceTime, ∫ ω, |Y ω q.1 * Y ω q.2| ∂P ≤ M := by
    intro q
    have hx : Integrable (fun ω => Y ω q.1 * Y ω q.1) P := (hL2 q.1).integrable_mul (hL2 q.1)
    have hy : Integrable (fun ω => Y ω q.2 * Y ω q.2) P := (hL2 q.2).integrable_mul (hL2 q.2)
    have hxy : Integrable (fun ω => Y ω q.1 * Y ω q.2) P := (hL2 q.1).integrable_mul (hL2 q.2)
    calc ∫ ω, |Y ω q.1 * Y ω q.2| ∂P
        ≤ ∫ ω, (Y ω q.1 * Y ω q.1 + Y ω q.2 * Y ω q.2) / 2 ∂P := by
          refine integral_mono hxy.abs ((hx.add hy).div_const 2) fun ω => ?_
          rw [abs_mul]
          nlinarith [sq_nonneg (|Y ω q.1| - |Y ω q.2|), abs_mul_abs_self (Y ω q.1),
            abs_mul_abs_self (Y ω q.2)]
      _ ≤ M := by
          rw [integral_div, integral_add hx hy]
          linarith [hM q.1, hM q.2]
  have hG := integrable_uncurry_mul_of_bound (P := P)
    (μ := (volume.prod volume : Measure (SpaceTime × SpaceTime)))
    (hg.mul_prod hg) (Y := fun ω q => Y ω q.1 * Y ω q.2) hYj.aestronglyMeasurable
    (fun q => (hL2 q.1).integrable_mul (hL2 q.2)) hbound
  calc ∫ ω, |∫ w, Y ω w * g w| ^ 2 ∂P
      = ∫ ω, (∫ q : SpaceTime × SpaceTime, (g q.1 * g q.2) * (Y ω q.1 * Y ω q.2)) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall hsq)
    _ = ∫ q : SpaceTime × SpaceTime, (∫ ω, (g q.1 * g q.2) * (Y ω q.1 * Y ω q.2) ∂P) :=
        integral_integral_swap hG
    _ = ∫ q : SpaceTime × SpaceTime, g q.1 * g q.2 * Φ q.1 q.2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only
        rw [integral_const_mul, hcov]
    _ ≤ |∫ q : SpaceTime × SpaceTime, g q.1 * g q.2 * Φ q.1 q.2| := le_abs_self _
    _ ≤ ∫ q : SpaceTime × SpaceTime, ‖g q.1 * g q.2 * Φ q.1 q.2‖ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun q : SpaceTime × SpaceTime => g q.1 * g q.2 * Φ q.1 q.2)
    _ = _ := by simp only [norm_mul, Real.norm_eq_abs]

end RegularityStructures

end
