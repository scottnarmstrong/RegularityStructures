/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePathwiseContinuity
public import RegularityStructures.Torus.KernelBoundsGeometry
public import RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Polynomial growth gives an exponentially integrable past

A polynomial envelope is dominated by an exponential of half the rate. The remaining exponential is
integrable on every past half-line. This discharges the analytic integrability input for the
deterministic potential-existence clause of the convergence of the noise potentials
(`phi43Noise_cauchy`); the kernel is the stationary massive heat kernel of equation (2.2) of the
statement.
-/

public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

private theorem polynomial_exp_majorant (q : ℕ) (a : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ≤ a,
      exp t * (1 + |t|) ^ q ≤ D * exp ((1 / 2 : ℝ) * t) := by
  let A : ℝ := (2 : ℝ) ^ q * (q.factorial : ℝ)
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  refine ⟨A * exp (1 / 2 + max a 0), mul_nonneg hA (exp_nonneg _), ?_⟩
  intro t ht
  have hfac : (0 : ℝ) < (q.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hpow : (1 + |t|) ^ q ≤ A * exp ((1 + |t|) / 2) := by
    have h := (div_le_iff₀ hfac).mp
      (pow_div_factorial_le_exp ((1 + |t|) / 2) (by positivity) q)
    have hscale : (1 + |t|) ^ q = (2 : ℝ) ^ q * ((1 + |t|) / 2) ^ q := by
      rw [← mul_pow]
      congr 1
      ring
    rw [hscale]
    exact (mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num) _)).trans_eq (by dsimp [A]; ring)
  have ht_bound : t + (1 + |t|) / 2 ≤ 1 / 2 + max a 0 + (1 / 2 : ℝ) * t := by
    by_cases htn : t ≤ 0
    · rw [abs_of_nonpos htn]
      linarith only [le_max_right a 0]
    · rw [abs_of_nonneg (le_of_not_ge htn)]
      linarith only [ht, le_max_left a 0]
  calc
    _ ≤ exp t * (A * exp ((1 + |t|) / 2)) :=
      mul_le_mul_of_nonneg_left hpow (exp_nonneg _)
    _ = A * exp (t + (1 + |t|) / 2) := by rw [exp_add]; ring
    _ ≤ A * exp (1 / 2 + max a 0 + (1 / 2 : ℝ) * t) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr ht_bound) hA
    _ = _ := by rw [exp_add]; ring

theorem weighted_past_integrable_of_polynomial_time_bound
    {f : SpaceTime → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (q : ℕ)
    (hb : ∀ z : SpaceTime, |f z| ≤ C * (1 + |z.1|) ^ q) (a : ℝ) :
    IntegrableOn (fun z : SpaceTime => exp z.1 * |f z|) {z : SpaceTime | z.1 ≤ a} := by
  obtain ⟨D, hD, hbound⟩ := polynomial_exp_majorant q a
  have ht : Integrable ((Iic a).indicator (fun t : ℝ => exp ((1 / 2 : ℝ) * t))) :=
    (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2) a).integrable_indicator
      measurableSet_Iic
  have hi := (ht.comp_fst (volume : Measure Torus3)).const_mul (C * D)
  apply hi.integrableOn.mono'
    (((measurable_exp.comp measurable_fst).mul hf.norm).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_fst measurable_const)] with z hz
  change ‖exp z.1 * |f z|‖ ≤ C * D *
    (Iic a).indicator (fun t : ℝ => exp ((1 / 2 : ℝ) * t)) z.1
  rw [indicator_of_mem (show z.1 ∈ Iic a from hz),
    Real.norm_of_nonneg (mul_nonneg (exp_nonneg _) (abs_nonneg _))]
  calc
    _ ≤ exp z.1 * (C * (1 + |z.1|) ^ q) :=
      mul_le_mul_of_nonneg_left (hb z) (exp_nonneg _)
    _ = C * (exp z.1 * (1 + |z.1|) ^ q) := by ring
    _ ≤ C * (D * exp ((1 / 2 : ℝ) * z.1)) :=
      mul_le_mul_of_nonneg_left (hbound z.1 hz) hC
    _ = _ := by ring

theorem polynomial_time_bound_of_polynomialLift_growth
    {f : SpaceTime → ℝ} {Cg : ℝ} {q : ℕ}
    (hg : ∀ z : ParabolicSpace, |f (z.1, torusProj z.2)| ≤
      Cg * (1 + parabolicNorm z) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SpaceTime, |f z| ≤ C * (1 + |z.1|) ^ q := by
  let C := max Cg 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C * (5 : ℝ) ^ q, mul_nonneg hC (pow_nonneg (by norm_num) _), ?_⟩
  intro z
  have hsum : (∑ i : Fin 3, |torusCenteredRep z.2 i|) ≤ 3 := by
    calc
      _ ≤ ∑ _i : Fin 3, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := torusCenteredRep_mem_Icc z.2 i
        exact abs_le.mpr ⟨by linarith only [hi.1], by linarith only [hi.2]⟩
      _ = 3 := by norm_num
  have hsqrt : √|z.1| ≤ 1 + |z.1| := by
    rw [sqrt_le_left (by positivity)]
    nlinarith only [sq_nonneg |z.1|, abs_nonneg z.1]
  have hsize : 1 + parabolicNorm (z.1, torusCenteredRep z.2) ≤ 5 * (1 + |z.1|) := by
    change 1 + (√|z.1| + ∑ i, |torusCenteredRep z.2 i|) ≤ _
    linarith only [hsum, hsqrt, abs_nonneg z.1]
  have h := hg (z.1, torusCenteredRep z.2)
  rw [torusProj_torusCenteredRep] at h
  calc
    _ ≤ Cg * (1 + parabolicNorm (z.1, torusCenteredRep z.2)) ^ q := h
    _ ≤ C * (1 + parabolicNorm (z.1, torusCenteredRep z.2)) ^ q :=
      mul_le_mul_of_nonneg_right (le_max_left _ _)
        (pow_nonneg (by linarith only [parabolicNorm_nonneg (z.1, torusCenteredRep z.2)]) _)
    _ ≤ C * (5 * (1 + |z.1|)) ^ q := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith only [parabolicNorm_nonneg (z.1, torusCenteredRep z.2)]) hsize _) hC
    _ = _ := by rw [mul_pow]; ring

end RegularityStructures.Phi43

end
