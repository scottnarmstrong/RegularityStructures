/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.Poincare
public import RegularityStructures.Probability.GaussianGrowthIntegrability
public import RegularityStructures.Probability.GaussianMoments
public import RegularityStructures.Probability.GaussianIBP
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Gaussian integration by parts for polynomials

For the standard Gaussian `γ = standardGaussianMeasure n` and a polynomial `F` in `n` variables,
`∫ x_i F dγ = ∫ ∂_i F dγ` (`integral_eval_X_mul_eq_pderiv`).  The proof uses the one-dimensional
moment recursion `∫ t^(a+1) = a ∫ t^(a-1)` for `N(0,1)`, which is obtained from the existing
one-dimensional Gaussian integration by parts, and the product structure of `γ` on monomials.
Every polynomial is integrable (`integrable_eval_standardGaussianMeasure`) and lies in every
finite Lebesgue space of `γ` (`memLp_eval_standardGaussianMeasure`).
-/

public section

open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal NNReal

namespace RegularityStructures

private lemma norm_fderiv_real_le_abs_apply_one (L : ℝ →L[ℝ] ℝ) : ‖L‖ ≤ |L 1| := by
  apply L.opNorm_le_bound (abs_nonneg _)
  intro x
  rw [show x = x • (1 : ℝ) by simp, map_smul]
  simp [Real.norm_eq_abs, mul_comm]

/-- The one-dimensional moment recursion for the standard Gaussian. -/
theorem integral_pow_succ_gaussianReal_one (a : ℕ) :
    ∫ t, t ^ (a + 1) ∂(gaussianReal 0 1) = a * ∫ t, t ^ (a - 1) ∂(gaussianReal 0 1) := by
  have hcont : ContDiff ℝ 1 (fun t : ℝ => t ^ a) := (contDiff_id.pow a)
  have hderiv (x : ℝ) : fderiv ℝ (fun t : ℝ => t ^ a) x 1 = a * x ^ (a - 1) := by
    rw [fderiv_apply_one_eq_deriv]
    exact (hasDerivAt_pow a x).deriv
  have hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |x ^ a| + ‖fderiv ℝ (fun t : ℝ => t ^ a) x‖ ≤ C * (1 + ‖x‖) ^ N := by
    refine ⟨1 + a, a, by positivity, fun x => ?_⟩
    have h1 : ‖fderiv ℝ (fun t : ℝ => t ^ a) x‖ ≤ a * |x| ^ (a - 1) := by
      refine (norm_fderiv_real_le_abs_apply_one _).trans ?_
      rw [hderiv, abs_mul, abs_pow, Nat.abs_cast]
    have hx : |x| ≤ 1 + ‖x‖ := by rw [Real.norm_eq_abs]; linarith
    have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : |x| ^ (a - 1) ≤ (1 + ‖x‖) ^ a :=
      (pow_le_pow_left₀ (abs_nonneg x) hx _).trans (pow_le_pow_right₀ hx1 (Nat.sub_le a 1))
    have h3 : |x ^ a| ≤ (1 + ‖x‖) ^ a := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg x) hx _
    have h4 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith [mul_le_mul_of_nonneg_left h2 h4]
  have hint : ∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) (gaussianReal 0 1) := fun k =>
    integrable_pow_gaussianReal 1 0 k
  have hibp := gaussian_integration_by_parts_one_dimensional hcont hgrowth
    (integrable_gaussian_weight_of_integrable (hint a))
    (by
      simp_rw [hderiv]
      exact integrable_gaussian_weight_of_integrable
        (f := fun t : ℝ => (a : ℝ) * t ^ (a - 1)) ((hint (a - 1)).const_mul _))
    (integrable_gaussian_weight_of_integrable (f := fun t : ℝ => t * t ^ a)
      (by simpa [pow_succ'] using hint (a + 1)))
  simp_rw [hderiv, ← pow_succ'] at hibp
  rw [hibp, integral_const_mul]

variable {n : ℕ}

instance isProbabilityMeasure_standardGaussianMeasure (n : ℕ) :
    IsProbabilityMeasure (standardGaussianMeasure n) := by
  unfold standardGaussianMeasure
  infer_instance

private lemma eval_monomial_eq_prod (x : Fin n → ℝ) (s : Fin n →₀ ℕ) (c : ℝ) :
    eval x (monomial s c) = c * ∏ i, x i ^ s i := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]

private lemma integrable_prod_pow (a : Fin n → ℕ) :
    Integrable (fun x : Fin n → ℝ => ∏ i, x i ^ a i) (standardGaussianMeasure n) :=
  Integrable.fintype_prod (f := fun i (t : ℝ) => t ^ a i) (μ := fun _ => gaussianReal 0 1)
    (fun i => integrable_pow_gaussianReal 1 0 (a i))

private lemma integral_prod_pow (a : Fin n → ℕ) :
    ∫ x, ∏ i, x i ^ a i ∂(standardGaussianMeasure n) =
      ∏ i, ∫ t, t ^ a i ∂(gaussianReal 0 1) :=
  integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => t ^ a i) (μ := fun _ => gaussianReal 0 1)

/-- Every polynomial is integrable for the standard Gaussian. -/
theorem integrable_eval_standardGaussianMeasure (p : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x => eval x p) (standardGaussianMeasure n) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    simp_rw [eval_monomial_eq_prod]
    exact (integrable_prod_pow _).const_mul c
  | add p q hp hq =>
    simp_rw [map_add]
    exact hp.add hq

private lemma X_mul_prod_pow (i : Fin n) (x : Fin n → ℝ) (s : Fin n →₀ ℕ) :
    x i * ∏ j, x j ^ s j = ∏ j, x j ^ (s j + if j = i then 1 else 0) := by
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib]
  have h : ∏ j, x j ^ (if j = i then 1 else 0) = x i := by simp [pow_ite]
  rw [h, mul_comm]

private lemma integral_eval_X_mul_monomial (i : Fin n) (s : Fin n →₀ ℕ) (c : ℝ) :
    ∫ x, eval x (X i * monomial s c) ∂(standardGaussianMeasure n) =
      ∫ x, eval x (pderiv i (monomial s c)) ∂(standardGaussianMeasure n) := by
  have hL : ∀ x : Fin n → ℝ, eval x (X i * monomial s c) =
      c * ∏ j, x j ^ (s j + if j = i then 1 else 0) := by
    intro x
    rw [eval_mul, eval_X, eval_monomial_eq_prod, ← X_mul_prod_pow]
    ring
  have hR : ∀ x : Fin n → ℝ, eval x (pderiv i (monomial s c)) =
      (c * s i) * ∏ j, x j ^ (s - Finsupp.single i 1 : Fin n →₀ ℕ) j := by
    intro x
    rw [pderiv_monomial, eval_monomial_eq_prod]
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul,
    integral_prod_pow (fun j => s j + if j = i then 1 else 0),
    integral_prod_pow (fun j => (s - Finsupp.single i 1 : Fin n →₀ ℕ) j)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => ∫ t, t ^ (s - Finsupp.single i 1 : Fin n →₀ ℕ) j
      ∂(gaussianReal 0 1)) (Finset.mem_univ i)]
  have herase : ∏ j ∈ Finset.univ.erase i, ∫ t, t ^ (s j + if j = i then 1 else 0)
      ∂(gaussianReal 0 1) = ∏ j ∈ Finset.univ.erase i, ∫ t, t ^ (s - Finsupp.single i 1 : Fin n →₀ ℕ) j
      ∂(gaussianReal 0 1) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [hji]
  rw [herase]
  have hi : ∫ t, t ^ (s i + if i = i then 1 else 0) ∂(gaussianReal 0 1) =
      s i * ∫ t, t ^ (s - Finsupp.single i 1 : Fin n →₀ ℕ) i ∂(gaussianReal 0 1) := by
    simpa using integral_pow_succ_gaussianReal_one (s i)
  rw [hi]
  ring

/-- Gaussian integration by parts for polynomials: `∫ x_i F dγ = ∫ ∂_i F dγ`. -/
theorem integral_eval_X_mul_eq_pderiv (i : Fin n) (F : MvPolynomial (Fin n) ℝ) :
    ∫ x, eval x (X i * F) ∂(standardGaussianMeasure n) =
      ∫ x, eval x (pderiv i F) ∂(standardGaussianMeasure n) := by
  induction F using MvPolynomial.induction_on' with
  | monomial s c => exact integral_eval_X_mul_monomial i s c
  | add p q hp hq =>
    rw [mul_add, map_add]
    simp_rw [map_add]
    rw [integral_add (integrable_eval_standardGaussianMeasure _)
        (integrable_eval_standardGaussianMeasure _),
      integral_add (integrable_eval_standardGaussianMeasure _)
        (integrable_eval_standardGaussianMeasure _), hp, hq]

/-- Every polynomial lies in every finite Lebesgue space of the standard Gaussian. -/
theorem memLp_eval_standardGaussianMeasure (p : MvPolynomial (Fin n) ℝ) {q : ℝ≥0∞}
    (hq : q ≠ ∞) : MemLp (fun x => eval x p) q (standardGaussianMeasure n) := by
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hq
  have hmeas : AEStronglyMeasurable (fun x => eval x p) (standardGaussianMeasure n) :=
    (MvPolynomial.continuous_eval p).aestronglyMeasurable
  have h2k : MemLp (fun x => eval x p) ((2 * (k + 1) : ℕ) : ℝ≥0∞) (standardGaussianMeasure n) := by
    rw [← integrable_norm_rpow_iff hmeas (by exact_mod_cast (by omega : 2 * (k + 1) ≠ 0))
      (ENNReal.natCast_ne_top _)]
    have : (fun x => ‖eval x p‖ ^ (((2 * (k + 1) : ℕ) : ℝ≥0∞).toReal)) =
        fun x => eval x (p ^ (2 * (k + 1))) := by
      funext x
      rw [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, map_pow]
      exact (Even.pow_abs ⟨k + 1, by ring⟩ _)
    rw [this]
    exact integrable_eval_standardGaussianMeasure _
  refine h2k.mono_exponent ?_
  refine hk.le.trans ?_
  exact_mod_cast (by omega : k ≤ 2 * (k + 1))

end RegularityStructures

end
