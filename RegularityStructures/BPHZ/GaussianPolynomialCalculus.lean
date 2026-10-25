/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialIBP
public import RegularityStructures.Probability.GaussianPoincareN
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Calculus and growth for polynomial functions on `ℝⁿ`

For `p : MvPolynomial (Fin n) ℝ` the function `x ↦ eval x p` is smooth
(`contDiff_eval`), its coordinate derivative is the evaluation of the formal partial derivative
(`coordinateDerivative_eval`), and it has polynomial growth together with its derivative
(`exists_growth_eval`).  Consequently the Gaussian Poincaré inequality applies to every polynomial
(`gaussian_poincare_eval`).
-/

public section

open MvPolynomial MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {n : ℕ}

theorem contDiff_eval (p : MvPolynomial (Fin n) ℝ) {N : WithTop ℕ∞} :
    ContDiff ℝ N (fun x : Fin n → ℝ => eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℝ ℝ i)

theorem fderiv_eval_single (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => eval y p) x (Pi.single i 1) = eval x (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have hdp := (contDiff_eval p (N := 1)).differentiable one_ne_zero x
    have hdq := (contDiff_eval q (N := 1)).differentiable one_ne_zero x
    have : (fun y : Fin n → ℝ => eval y (p + q)) =
        (fun y => eval y p) + (fun y => eval y q) := by funext y; simp
    rw [this, fderiv_add hdp hdq, map_add]
    simp only [add_apply, hp, hq, map_add]
  | mul_X p j hp =>
    have hdp := (contDiff_eval p (N := 1)).differentiable one_ne_zero x
    have hdj : DifferentiableAt ℝ (fun y : Fin n → ℝ => y j) x :=
      (hasFDerivAt_apply j x).differentiableAt
    have : (fun y : Fin n → ℝ => eval y (p * X j)) =
        (fun y => eval y p) * (fun y => y j) := by funext y; simp
    rw [this, fderiv_mul hdp hdj]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [(hasFDerivAt_apply j x).fderiv, hp, pderiv_mul]
    by_cases hij : j = i
    · subst hij; simp [pderiv_X]; ring
    · simp [pderiv_X, hij]; ring

theorem coordinateDerivative_eval (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y : Fin n → ℝ => eval y p) i x = eval x (pderiv i p) :=
  fderiv_eval_single p i x

theorem coordinateEnergy_eval (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    coordinateEnergy (fun y : Fin n → ℝ => eval y p) x = ∑ i, eval x (pderiv i p) ^ 2 := by
  unfold coordinateEnergy
  simp_rw [coordinateDerivative_eval]

private def HasPolyBound (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : Fin n → ℝ, |g x| ≤ C * (1 + ‖x‖) ^ N

private lemma one_le_one_add_norm (x : Fin n → ℝ) : 1 ≤ 1 + ‖x‖ := by
  linarith [norm_nonneg x]

private lemma HasPolyBound.add {g h : (Fin n → ℝ) → ℝ} (hg : HasPolyBound g)
    (hh : HasPolyBound h) : HasPolyBound (fun x => g x + h x) := by
  obtain ⟨C₁, N₁, hC₁, hg⟩ := hg
  obtain ⟨C₂, N₂, hC₂, hh⟩ := hh
  refine ⟨C₁ + C₂, N₁ + N₂, by positivity, fun x => ?_⟩
  have h1 : (1 + ‖x‖) ^ N₁ ≤ (1 + ‖x‖) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ (one_le_one_add_norm x) (Nat.le_add_right _ _)
  have h2 : (1 + ‖x‖) ^ N₂ ≤ (1 + ‖x‖) ^ (N₁ + N₂) :=
    pow_le_pow_right₀ (one_le_one_add_norm x) (Nat.le_add_left _ _)
  calc |g x + h x| ≤ |g x| + |h x| := abs_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ N₁ + C₂ * (1 + ‖x‖) ^ N₂ := add_le_add (hg x) (hh x)
    _ ≤ (C₁ + C₂) * (1 + ‖x‖) ^ (N₁ + N₂) := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h1 hC₁) (mul_le_mul_of_nonneg_left h2 hC₂)

private lemma HasPolyBound.sum {ι : Type*} (s : Finset ι) {g : ι → (Fin n → ℝ) → ℝ}
    (hg : ∀ i ∈ s, HasPolyBound (g i)) : HasPolyBound (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, fun x => by simp⟩
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

private lemma hasPolyBound_eval (p : MvPolynomial (Fin n) ℝ) :
    HasPolyBound (fun x : Fin n → ℝ => eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨|a|, 0, abs_nonneg _, fun x => by simp⟩
  | add p q hp hq => simpa using hp.add hq
  | mul_X p j hp =>
    obtain ⟨C, N, hC, hb⟩ := hp
    refine ⟨C, N + 1, hC, fun x => ?_⟩
    have hxj : |x j| ≤ 1 + ‖x‖ := by
      have := norm_le_pi_norm x j
      rw [Real.norm_eq_abs] at this
      linarith
    simp only [map_mul, eval_X, abs_mul]
    calc |eval x p| * |x j| ≤ C * (1 + ‖x‖) ^ N * (1 + ‖x‖) :=
          mul_le_mul (hb x) hxj (abs_nonneg _) (by have := hb x; positivity)
      _ = C * (1 + ‖x‖) ^ (N + 1) := by ring

private lemma norm_clm_pi_le_sum (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, |L (Pi.single i 1)| := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => abs_nonneg _) fun v => ?_
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [Real.norm_eq_abs]
  conv_lhs => rw [hv, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  calc |∑ i, v i * L (Pi.single i 1)| ≤ ∑ i, |v i * L (Pi.single i 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖v‖ * |L (Pi.single i 1)| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm v i) (abs_nonneg _)
    _ = (∑ i, |L (Pi.single i 1)|) * ‖v‖ := by rw [← Finset.mul_sum]; ring

/-- A polynomial and its derivative have polynomial growth. -/
theorem exists_growth_eval (p : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : Fin n → ℝ,
      |eval x p| + ‖fderiv ℝ (fun y : Fin n → ℝ => eval y p) x‖ ≤ C * (1 + ‖x‖) ^ N := by
  have hsum : HasPolyBound (fun x : Fin n → ℝ => |eval x p| + ∑ i, |eval x (pderiv i p)|) := by
    refine HasPolyBound.add ?_ (HasPolyBound.sum _ fun i _ => ?_)
    · obtain ⟨C, N, hC, hb⟩ := hasPolyBound_eval p
      exact ⟨C, N, hC, fun x => by simpa using hb x⟩
    · obtain ⟨C, N, hC, hb⟩ := hasPolyBound_eval (pderiv i p)
      exact ⟨C, N, hC, fun x => by simpa using hb x⟩
  obtain ⟨C, N, hC, hb⟩ := hsum
  refine ⟨C, N, hC, fun x => ?_⟩
  have h1 := norm_clm_pi_le_sum (fderiv ℝ (fun y : Fin n → ℝ => eval y p) x)
  simp_rw [fderiv_eval_single] at h1
  have h2 := hb x
  rw [abs_of_nonneg (by positivity)] at h2
  linarith

/-- The Gaussian Poincaré inequality for polynomials. -/
theorem gaussian_poincare_eval (p : MvPolynomial (Fin n) ℝ) :
    Var[fun x : Fin n → ℝ => eval x p; standardGaussianMeasure n] ≤
      ∫ x, ∑ i, eval x (pderiv i p) ^ 2 ∂(standardGaussianMeasure n) := by
  have h := gaussian_poincare_standard (contDiff_eval p (N := 1)) (exists_growth_eval p)
  simpa [coordinateEnergy_eval] using h

end RegularityStructures

end
