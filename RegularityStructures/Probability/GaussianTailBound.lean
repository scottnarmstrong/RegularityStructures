/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianTail

/-!
# Polynomially weighted Gaussian tails

This module transfers the scalar Gaussian tail estimate to an integrable function whose Gaussian
weighted tail is polynomially bounded.  It is the estimate used by the explicit Stein primitive.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

namespace RegularityStructures

private lemma integrableOn_gaussian_nat_pow' {k : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => t ^ k * rexp (-t ^ 2 / 2)) (Ioi a) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
    (by norm_num : (0 : ℝ) < 1 / 2) (s := (k : ℝ))
    (by
      have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith)
  have h' : IntegrableOn
      (fun t : ℝ => t ^ (k : ℝ) * rexp (-(1 / 2 : ℝ) * t ^ 2)) (Ioi a) :=
    h.mono_set (Ioi_subset_Ioi ha)
  convert h' using 1
  · funext t
    rw [Real.rpow_natCast]
    congr 2
    ring

theorem gaussian_tail_integral_bound_of_polynomial_weight {q : ℝ → ℝ}
    (hq : Integrable q (volume : Measure ℝ))
    (hqbound : ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
      ∀ t : ℝ, |q t| ≤ K * (1 + |t|) ^ N * rexp (-t ^ 2 / 2)) :
    ∃ D : ℝ, ∃ N : ℕ, 0 ≤ D ∧ ∀ a : ℝ, 1 ≤ a →
      |∫ t in Ioi a, q t| ≤ D * (1 + a ^ N) * rexp (-a ^ 2 / 2) := by
  rcases hqbound with ⟨K, N, hK, hqbound⟩
  rcases gaussian_tail_nat_pow_bound (k := N) with ⟨T, hT, htail⟩
  refine ⟨K * 2 ^ N * T, N, ?_, ?_⟩
  · positivity
  intro a ha
  have hqI : IntegrableOn q (Ioi a) := hq.integrableOn
  have hmajor : IntegrableOn
      (fun t : ℝ => K * 2 ^ N * (t ^ N * rexp (-t ^ 2 / 2))) (Ioi a) := by
    have hbase := integrableOn_gaussian_nat_pow' (k := N)
      (le_trans (by norm_num) ha)
    simpa [IntegrableOn, mul_assoc] using (hbase.const_mul (K * 2 ^ N))
  have hnorm : IntegrableOn (fun t : ℝ => |q t|) (Ioi a) := hqI.norm
  have hmono : ∫ t in Ioi a, |q t| ≤
      ∫ t in Ioi a, K * 2 ^ N * (t ^ N * rexp (-t ^ 2 / 2)) := by
    apply integral_mono_ae hnorm hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hta : a < t := ht
    have ht1 : 1 ≤ t := le_trans ha hta.le
    have hpow : (1 + |t|) ^ N ≤ (2 * t) ^ N := by
      rw [abs_of_nonneg (le_trans (le_trans (by norm_num) ha) hta.le)]
      apply pow_le_pow_left₀
      · linarith
      · linarith
    have hbase : |q t| ≤ K * (2 * t) ^ N * rexp (-t ^ 2 / 2) := by
      calc
        |q t| ≤ K * (1 + |t|) ^ N * rexp (-t ^ 2 / 2) := hqbound t
        _ ≤ K * (2 * t) ^ N * rexp (-t ^ 2 / 2) := by
          have hmul := mul_le_mul_of_nonneg_left hpow hK
          exact mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
    calc
      |q t| ≤ K * (2 * t) ^ N * rexp (-t ^ 2 / 2) := hbase
      _ = K * 2 ^ N * (t ^ N * rexp (-t ^ 2 / 2)) := by
        rw [mul_pow]
        ring
  calc
    |∫ t in Ioi a, q t| ≤ ∫ t in Ioi a, |q t| := norm_integral_le_integral_norm q
    _ ≤ ∫ t in Ioi a, K * 2 ^ N * (t ^ N * rexp (-t ^ 2 / 2)) := hmono
    _ = K * 2 ^ N * (∫ t in Ioi a, t ^ N * rexp (-t ^ 2 / 2)) := by
      rw [integral_const_mul]
    _ ≤ K * 2 ^ N * (T * (1 + a ^ N) * rexp (-a ^ 2 / 2)) := by
      gcongr
      exact htail a ha |>.2
    _ = (K * 2 ^ N * T) * (1 + a ^ N) * rexp (-a ^ 2 / 2) := by ring

end RegularityStructures

end
