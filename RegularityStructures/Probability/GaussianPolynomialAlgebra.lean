/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPolynomial

/-!
# Algebra of explicit polynomial bounds

These elementary closure lemmas keep the polynomial-growth hypotheses visible while making the
many integrability arguments in the Stein proof modular.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

theorem polynomial_bound_const (c : ℝ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |c| ≤ C * (1 + |x|) ^ N := by
  refine ⟨|c|, 0, abs_nonneg c, ?_⟩
  intro x
  simp

theorem polynomial_bound_id :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |x| ≤ C * (1 + |x|) ^ N := by
  refine ⟨1, 1, by norm_num, ?_⟩
  intro x
  norm_num [pow_one]

theorem polynomial_bound_add {f g : ℝ → ℝ}
    (hf : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N)
    (hg : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |g x| ≤ C * (1 + |x|) ^ N) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ,
      |f x + g x| ≤ C * (1 + |x|) ^ N := by
  rcases hf with ⟨C, N, hC, hf⟩
  rcases hg with ⟨D, M, hD, hg⟩
  refine ⟨C + D, N + M, add_nonneg hC hD, ?_⟩
  intro x
  have hbase : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hN : (1 + |x|) ^ N ≤ (1 + |x|) ^ (N + M) := by
    exact pow_le_pow_right₀ hbase (Nat.le_add_right _ _)
  have hM : (1 + |x|) ^ M ≤ (1 + |x|) ^ (N + M) := by
    exact pow_le_pow_right₀ hbase (Nat.le_add_left _ _)
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C * (1 + |x|) ^ N + D * (1 + |x|) ^ M := add_le_add (hf x) (hg x)
    _ ≤ C * (1 + |x|) ^ (N + M) + D * (1 + |x|) ^ (N + M) := by
      gcongr
    _ = (C + D) * (1 + |x|) ^ (N + M) := by ring

theorem polynomial_bound_sub {f g : ℝ → ℝ}
    (hf : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N)
    (hg : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |g x| ≤ C * (1 + |x|) ^ N) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ,
      |f x - g x| ≤ C * (1 + |x|) ^ N := by
  have hneg : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |-g x| ≤ C * (1 + |x|) ^ N := by
    rcases hg with ⟨C, N, hC, hg⟩
    exact ⟨C, N, hC, by simpa only [abs_neg] using hg⟩
  simpa only [sub_eq_add_neg] using polynomial_bound_add hf hneg

theorem polynomial_bound_sum_norm {f g : ℝ → ℝ}
    (hf : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N)
    (hg : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |g x| ≤ C * (1 + |x|) ^ N) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ,
      |f x| + |g x| ≤ C * (1 + |x|) ^ N := by
  rcases hf with ⟨C, N, hC, hf⟩
  rcases hg with ⟨D, M, hD, hg⟩
  refine ⟨C + D, N + M, add_nonneg hC hD, ?_⟩
  intro x
  have hbase : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hN : (1 + |x|) ^ N ≤ (1 + |x|) ^ (N + M) :=
    pow_le_pow_right₀ hbase (Nat.le_add_right _ _)
  have hM : (1 + |x|) ^ M ≤ (1 + |x|) ^ (N + M) :=
    pow_le_pow_right₀ hbase (Nat.le_add_left _ _)
  calc
    |f x| + |g x| ≤ C * (1 + |x|) ^ N + D * (1 + |x|) ^ M :=
      add_le_add (hf x) (hg x)
    _ ≤ C * (1 + |x|) ^ (N + M) + D * (1 + |x|) ^ (N + M) := by
      gcongr
    _ = (C + D) * (1 + |x|) ^ (N + M) := by ring

theorem polynomial_bound_mul {f g : ℝ → ℝ}
    (hf : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N)
    (hg : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |g x| ≤ C * (1 + |x|) ^ N) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ,
      |f x * g x| ≤ C * (1 + |x|) ^ N := by
  rcases hf with ⟨C, N, hC, hf⟩
  rcases hg with ⟨D, M, hD, hg⟩
  refine ⟨C * D, N + M, mul_nonneg hC hD, ?_⟩
  intro x
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C * (1 + |x|) ^ N) * (D * (1 + |x|) ^ M) :=
      mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)
    _ = C * D * ((1 + |x|) ^ N * (1 + |x|) ^ M) := by ring
    _ = (C * D) * (1 + |x|) ^ (N + M) := by rw [← pow_add]

theorem polynomial_bound_pow {f : ℝ → ℝ}
    (hf : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N)
    (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ,
      |f x ^ k| ≤ C * (1 + |x|) ^ N := by
  induction k with
  | zero =>
      simpa using polynomial_bound_const (1 : ℝ)
  | succ k ih =>
      simpa [pow_succ] using polynomial_bound_mul ih hf

theorem integrable_continuous_polynomial_bound_gaussian {f : ℝ → ℝ}
    (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N) :
    Integrable f (gaussianReal 0 1) := by
  apply integrable_polynomially_bounded_gaussian hf.measurable.aestronglyMeasurable
  rcases hgrowth with ⟨C, N, hC, hbound⟩
  exact ⟨C, N, hC, by simpa [Real.norm_eq_abs] using hbound⟩

theorem memLp_continuous_polynomial_bound_gaussian {f : ℝ → ℝ}
    (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N) :
    MemLp f 2 (gaussianReal 0 1) := by
  exact memLp_of_polynomial_bound_gaussian hf.measurable.aestronglyMeasurable hgrowth

theorem integrable_continuous_polynomial_weight {f : ℝ → ℝ}
    (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N) :
    Integrable (fun x => f x * gaussianPDFReal 0 1 x) (volume : Measure ℝ) := by
  exact integrable_gaussian_weight_of_integrable
    (integrable_continuous_polynomial_bound_gaussian hf hgrowth)

end RegularityStructures

end
