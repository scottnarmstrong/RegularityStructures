/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialCalculus
public import RegularityStructures.Probability.LpSpectralGapDyadic

/-!
# Dyadic `L^p` spectral gap for Gaussian polynomials

For a polynomial `f` in `n` variables and `γ = standardGaussianMeasure n`,
`E[|f - E f|^(2^(k+1))] ≤ C^(2^(k+1)) E[|∇f|^(2^(k+1))]` with `C = 2 (2^(k+1))^2`, independent of
`n` and `f` (`integral_abs_sub_mean_pow_le`).  This is the finite-dimensional counterpart of
`whiteNoise_cylindrical_lp_spectral_gap_dyadic`: the Gaussian Poincaré inequality is applied to
powers of the centred polynomial and iterated by `lp_spectral_gap_dyadic`.  For polynomials every
integrability hypothesis of the abstract iteration holds automatically.
-/

public section

open MvPolynomial MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RegularityStructures

variable {n : ℕ}

theorem integrable_abs_pow_eval (p : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    Integrable (fun x => |eval x p| ^ r) (standardGaussianMeasure n) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have hmeas : AEStronglyMeasurable (fun x => eval x p) (standardGaussianMeasure n) :=
      (MvPolynomial.continuous_eval p).aestronglyMeasurable
    have := (integrable_norm_rpow_iff hmeas (p := (r : ℝ≥0∞)) (by simpa using hr.ne')
      (ENNReal.natCast_ne_top r)).2 (memLp_eval_standardGaussianMeasure p
        (ENNReal.natCast_ne_top r))
    simpa [Real.norm_eq_abs, Real.rpow_natCast] using this

theorem sq_integral_le_integral_sq_eval (p : MvPolynomial (Fin n) ℝ) :
    (∫ x, eval x p ∂(standardGaussianMeasure n)) ^ 2 ≤
      ∫ x, eval x p ^ 2 ∂(standardGaussianMeasure n) := by
  have hL2 := memLp_eval_standardGaussianMeasure p (q := 2) (by simp)
  have h := variance_nonneg (fun x => eval x p) (standardGaussianMeasure n)
  rw [variance_eq_sub hL2] at h
  simp only [Pi.pow_apply] at h
  linarith

private lemma eval_sub_mean (f : MvPolynomial (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    eval x (f - C c) = eval x f - c := by simp

private lemma integral_eval_sub_mean (f : MvPolynomial (Fin n) ℝ) :
    ∫ x, eval x (f - C (∫ y, eval y f ∂(standardGaussianMeasure n))) ∂(standardGaussianMeasure n)
      = 0 := by
  simp_rw [eval_sub_mean]
  rw [integral_sub (integrable_eval_standardGaussianMeasure f) (integrable_const _)]
  simp

/-- The power-variance estimate for the centred polynomial, from the Gaussian Poincaré inequality. -/
private lemma variance_pow_le (f : MvPolynomial (Fin n) ℝ) (c : ℝ) (q : ℕ) :
    Var[fun x => eval x (f - C c) ^ q; standardGaussianMeasure n] ≤
      (q : ℝ) ^ 2 * ∫ x, |eval x (f - C c)| ^ (2 * q - 2) *
        (∑ i, eval x (pderiv i f ^ 2 : MvPolynomial (Fin n) ℝ)) ∂(standardGaussianMeasure n) := by
  have h := gaussian_poincare_eval ((f - C c) ^ q)
  have hfun : (fun x : Fin n → ℝ => eval x ((f - C c) ^ q)) =
      fun x => eval x (f - C c) ^ q := by funext x; simp
  rw [hfun] at h
  refine h.trans (le_of_eq ?_)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hd (i : Fin n) : eval x (pderiv i ((f - C c) ^ q)) =
      (q : ℝ) * eval x (f - C c) ^ (q - 1) * eval x (pderiv i f) := by
    rw [pderiv_pow, map_sub, pderiv_C, sub_zero]
    simp
  simp_rw [hd]
  have heven : Even (2 * q - 2) := ⟨q - 1, by omega⟩
  rw [heven.pow_abs]
  simp only [map_pow]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have : 2 * q - 2 = (q - 1) + (q - 1) := by omega
    rw [this, pow_add]
    ring

/-- **Dyadic `L^p` spectral gap for Gaussian polynomials**, with a constant independent of the
dimension and of the polynomial. -/
theorem integral_abs_sub_mean_pow_le (f : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    ∫ x, |eval x f - ∫ y, eval y f ∂(standardGaussianMeasure n)| ^ (2 ^ (k + 1))
        ∂(standardGaussianMeasure n) ≤
      (2 * ((2 ^ (k + 1) : ℕ) : ℝ) ^ 2) ^ (2 ^ (k + 1)) *
        ∫ x, coordinateEnergy (fun y : Fin n → ℝ => eval y f) x ^ (2 ^ k)
          ∂(standardGaussianMeasure n) := by
  set c := ∫ y, eval y f ∂(standardGaussianMeasure n) with hc
  set Gp : MvPolynomial (Fin n) ℝ := ∑ i, pderiv i f ^ 2 with hGp
  have hΓ : ∀ x : Fin n → ℝ, ∑ i, eval x (pderiv i f ^ 2 : MvPolynomial (Fin n) ℝ) =
      eval x Gp := fun x => by simp [hGp]
  have hCE : ∀ x : Fin n → ℝ, coordinateEnergy (fun y : Fin n → ℝ => eval y f) x =
      ∑ i, eval x (pderiv i f ^ 2 : MvPolynomial (Fin n) ℝ) := fun x => by
    rw [coordinateEnergy_eval]; simp
  have hmeasP : ∀ p : MvPolynomial (Fin n) ℝ,
      AEStronglyMeasurable (fun x => eval x p) (standardGaussianMeasure n) := fun p =>
    (MvPolynomial.continuous_eval p).aestronglyMeasurable
  have hΓnn : ∀ x : Fin n → ℝ, 0 ≤ eval x Gp := fun x => by
    rw [← hΓ]; exact Finset.sum_nonneg fun i _ => by simp [sq_nonneg]
  have hmemΓ : ∀ r : ℕ, ∀ q : ℝ≥0∞, q ≠ ∞ →
      MemLp (fun x => eval x Gp ^ r) q (standardGaussianMeasure n) := fun r q hq => by
    have := memLp_eval_standardGaussianMeasure (Gp ^ r) hq
    simpa using this
  have hY2 : ∀ r : ℕ, MemLp (fun x => eval x (f - C c) ^ r) 2 (standardGaussianMeasure n) :=
    fun r => by
      have := memLp_eval_standardGaussianMeasure ((f - C c) ^ r) (q := 2) (by simp)
      simpa only [map_pow] using this
  have hΓint : ∀ r : ℕ, Integrable (fun x => eval x Gp ^ r) (standardGaussianMeasure n) :=
    fun r => (hmemΓ r 1 (by simp)).integrable le_rfl
  have hholderY : ∀ q : ℕ, 2 ≤ q →
      MemLp (fun x => |eval x (f - C c)| ^ (2 * q - 2))
        (ENNReal.ofReal ((q : ℝ) / (q - 1))) (standardGaussianMeasure n) := fun q _ => by
    have heven : Even (2 * q - 2) := ⟨q - 1, by omega⟩
    have e : (fun x : Fin n → ℝ => |eval x (f - C c)| ^ (2 * q - 2)) =
        fun x => eval x ((f - C c) ^ (2 * q - 2)) := by
      funext x; rw [heven.pow_abs, map_pow]
    rw [e]
    exact memLp_eval_standardGaussianMeasure _ ENNReal.ofReal_ne_top
  have hΓsq : ∀ r : ℕ, (∫ x, eval x Gp ^ r ∂(standardGaussianMeasure n)) ^ 2 ≤
      ∫ x, eval x Gp ^ (2 * r) ∂(standardGaussianMeasure n) := fun r => by
    have h := sq_integral_le_integral_sq_eval (Gp ^ r)
    simp only [map_pow] at h
    have e : ∀ x : Fin n → ℝ, (eval x Gp ^ r) ^ 2 = eval x Gp ^ (2 * r) := fun x => by
      rw [← pow_mul, mul_comm]
    simp_rw [e] at h
    exact h
  obtain ⟨C, hC, hCle, hbound⟩ := lp_spectral_gap_dyadic
    (P := standardGaussianMeasure n) (Y := fun x => eval x (f - C c)) (Γ := fun x => eval x Gp)
    (hmeasP _) (fun r => integrable_abs_pow_eval _ r) hY2 hΓint
    (integral_eval_sub_mean f) (Filter.Eventually.of_forall hΓnn)
    (fun q _ => by
      simp_rw [← hΓ]
      exact variance_pow_le f c q)
    (fun q hq => integral_abs_pow_mul_le_holder hq (hholderY q hq)
      (memLp_eval_standardGaussianMeasure Gp ENNReal.ofReal_ne_top) (Filter.Eventually.of_forall hΓnn))
    hΓsq k
  simp_rw [hCE, hΓ]
  have hint_nn : 0 ≤ ∫ x, eval x Gp ^ (2 ^ k) ∂(standardGaussianMeasure n) :=
    integral_nonneg fun x => pow_nonneg (hΓnn x) _
  simp_rw [eval_sub_mean] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC hCle _) hint_nn)

end RegularityStructures

end
