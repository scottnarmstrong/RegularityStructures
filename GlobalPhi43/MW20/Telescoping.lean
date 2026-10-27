/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The summation step of MW20 §5.2.1

Finite collections of geometric increment bounds are controlled by a common
positive regularity. Equality of an individual regularity with the common
regularity is allowed. This is the numerical telescope component only; the
kernel factorisation and the identification of the limit with the smoothed
diagonal remain separate analytic obligations.
-/

public section

open Filter
open scoped Topology

namespace GlobalPhi43.MW20

/-- Non-strict exponent comparison, including the endpoint in MW20 Theorem 2.8. -/
theorem dyadic_ratio_le {γ a : ℝ} (ha : γ ≤ a) :
    (1 / 2 : ℝ) ^ a ≤ (1 / 2 : ℝ) ^ γ :=
  Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ha

/-- Collapse finitely many dyadic rates to the common regularity γ. -/
theorem sum_dyadic_rates_le {ι : Type*} (s : Finset ι) (B a : ι → ℝ) {γ : ℝ}
    (hB : ∀ i ∈ s, 0 ≤ B i) (ha : ∀ i ∈ s, γ ≤ a i) (n : ℕ) :
    (∑ i ∈ s, B i * ((1 / 2 : ℝ) ^ a i) ^ n) ≤
      (∑ i ∈ s, B i) * ((1 / 2 : ℝ) ^ γ) ^ n := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (dyadic_ratio_le (ha i hi)) n)
      (hB i hi)

/-- The numerical part of the reconstruction telescope, conditional on its
analytic increment bounds and its identified limit. No strict exponent slack
beyond `0 < γ` is used, and the constant is independent of the individual rates. -/
theorem reconstruction_telescope_bound {ι : Type*} (s : Finset ι) (B a : ι → ℝ)
    {γ : ℝ} (hγ : 0 < γ) (hB : ∀ i ∈ s, 0 ≤ B i)
    (ha : ∀ i ∈ s, γ ≤ a i) {u : ℕ → ℝ} {L : ℝ}
    (hinc : ∀ n, |u n - u (n + 1)| ≤ ∑ i ∈ s, B i * ((1 / 2 : ℝ) ^ a i) ^ n)
    (hlim : Tendsto u atTop (𝓝 L)) :
    |u 0 - L| ≤ (∑ i ∈ s, B i) / (1 - (1 / 2 : ℝ) ^ γ) := by
  have hratio : (1 / 2 : ℝ) ^ γ < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have hstep : ∀ n, dist (u n) (u (n + 1)) ≤
      (∑ i ∈ s, B i) * ((1 / 2 : ℝ) ^ γ) ^ n := by
    intro n
    rw [Real.dist_eq]
    exact (hinc n).trans (sum_dyadic_rates_le s B a hB ha n)
  exact dist_le_of_le_geometric_of_tendsto₀
    ((1 / 2 : ℝ) ^ γ) (∑ i ∈ s, B i) hratio hstep hlim

end GlobalPhi43.MW20

end
