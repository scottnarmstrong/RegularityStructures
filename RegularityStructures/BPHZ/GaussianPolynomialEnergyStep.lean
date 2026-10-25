/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialEnergyTower
public import RegularityStructures.BPHZ.GaussianPolynomialLpGap

/-!
# One step of the moment recursion for iterated gradient energies

Let `E = sqSum L` and `E' = sqSum (polyDerivs L)`, so that `|∇E|² ≤ 4 E E'` pointwise.  Writing
`q = 2^(k+1)` and `M = ∫ E^q dγ`, `M' = ∫ E'^q dγ`, the dyadic spectral gap for the polynomial `E`
together with Young's inequality `E^(q/2) E'^(q/2) ≤ E^q/(2t) + t E'^q/2` and the
convexity bound `(a + b)^q ≤ 2^(q-1) (a^q + b^q)` gives
`M ≤ 2 · 2^(q-1) μ^q + β M'`, where `μ` bounds the mean `∫ E dγ` and the constant `β` depends only
on `k` (`integral_pow_sqSum_le`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- An auxiliary constant of the moment step. -/
def momentStepW (k : ℕ) : ℝ :=
  2 ^ (2 ^ (k + 1) - 1) * (2 * ((2 ^ (k + 1) : ℕ) : ℝ) ^ 2) ^ (2 ^ (k + 1)) * 4 ^ (2 ^ k) / 2

/-- The constant multiplying the next-order moment in the moment step. -/
def momentStepConst (k : ℕ) : ℝ :=
  2 * momentStepW k * (2 * momentStepW k + 1)

end RegularityStructures

end

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

theorem momentStepW_nonneg (k : ℕ) : 0 ≤ momentStepW k := by
  unfold momentStepW; positivity

theorem momentStepConst_nonneg (k : ℕ) : 0 ≤ momentStepConst k := by
  unfold momentStepConst
  have := momentStepW_nonneg k
  positivity

private lemma amgm_aux (a b t : ℝ) (ht : 0 < t) :
    a * b ≤ a ^ 2 / (2 * t) + t * b ^ 2 / 2 := by
  have h : a ^ 2 / (2 * t) + t * b ^ 2 / 2 - a * b = (a - t * b) ^ 2 / (2 * t) := by
    field_simp; ring
  have : 0 ≤ (a - t * b) ^ 2 / (2 * t) := by positivity
  linarith

private lemma integrable_eval_pow (Q : MvPolynomial (Fin n) ℝ) (a : ℕ) :
    Integrable (fun x => eval x Q ^ a) (standardGaussianMeasure n) := by
  simpa using integrable_eval_standardGaussianMeasure (Q ^ a)

/-- One step of the moment recursion. -/
theorem integral_pow_sqSum_le (k : ℕ) (L : List (MvPolynomial (Fin n) ℝ)) (μ : ℝ)
    (hμ : gaussExp (sqSum L) ≤ μ) :
    ∫ x, eval x (sqSum L) ^ (2 ^ (k + 1)) ∂(standardGaussianMeasure n) ≤
      2 * (2 ^ (2 ^ (k + 1) - 1) * μ ^ (2 ^ (k + 1))) + momentStepConst k *
        ∫ x, eval x (sqSum (polyDerivs L)) ^ (2 ^ (k + 1)) ∂(standardGaussianMeasure n) := by
  set P := sqSum L with hP
  set P' := sqSum (polyDerivs L) with hP'
  set q : ℕ := 2 ^ (k + 1) with hq
  set r : ℕ := 2 ^ k with hr
  have hqr : q = 2 * r := by rw [hq, hr, pow_succ]; ring
  set w : ℝ := momentStepW k with hw
  have hw0 : 0 ≤ w := momentStepW_nonneg k
  set t : ℝ := 2 * w + 1 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  set Kc : ℝ := (2 * ((2 ^ (k + 1) : ℕ) : ℝ) ^ 2) ^ (2 ^ (k + 1)) with hKc
  set M : ℝ := ∫ x, eval x P ^ q ∂(standardGaussianMeasure n) with hM
  set M' : ℝ := ∫ x, eval x P' ^ q ∂(standardGaussianMeasure n) with hM'
  set m0 : ℝ := ∫ x, eval x P ∂(standardGaussianMeasure n) with hm0
  have hm0' : m0 = gaussExp P := rfl
  have hm0nn : 0 ≤ m0 := integral_nonneg fun x => eval_sqSum_nonneg x L
  have hm0μ : m0 ≤ μ := by rw [hm0']; exact hμ
  have hwdef : w = 2 ^ (q - 1) * Kc * 4 ^ r / 2 := by
    rw [hw, momentStepW]
  -- the Poincaré step
  have hH2 := integral_abs_sub_mean_pow_le P k
  rw [← hq, ← hm0] at hH2
  have hpt : ∀ x : Fin n → ℝ, coordinateEnergy (fun y : Fin n → ℝ => eval y P) x ^ r ≤
      4 ^ r / (2 * t) * eval x P ^ q + 4 ^ r * t / 2 * eval x P' ^ q := fun x => by
    have hce : coordinateEnergy (fun y : Fin n → ℝ => eval y P) x ≤
        4 * eval x P * eval x P' := by
      rw [coordinateEnergy_eval]
      exact sum_sq_pderiv_sqSum_le x L
    have hce0 : 0 ≤ coordinateEnergy (fun y : Fin n → ℝ => eval y P) x := by
      rw [coordinateEnergy_eval]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    calc coordinateEnergy (fun y : Fin n → ℝ => eval y P) x ^ r ≤ (4 * eval x P * eval x P') ^ r :=
          pow_le_pow_left₀ hce0 hce r
      _ = 4 ^ r * ((eval x P ^ r) * (eval x P' ^ r)) := by rw [mul_pow, mul_pow]; ring
      _ ≤ 4 ^ r * ((eval x P ^ r) ^ 2 / (2 * t) + t * (eval x P' ^ r) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (amgm_aux _ _ t ht0) (by positivity)
      _ = 4 ^ r / (2 * t) * eval x P ^ q + 4 ^ r * t / 2 * eval x P' ^ q := by
          rw [← pow_mul, ← pow_mul, hqr, mul_comm r 2]; ring
  have hint_ce : Integrable (fun x => coordinateEnergy (fun y : Fin n → ℝ => eval y P) x ^ r)
      (standardGaussianMeasure n) := by
    simp_rw [coordinateEnergy_eval_eq_sqSum]
    exact integrable_eval_pow _ r
  have hint_rhs : Integrable (fun x => 4 ^ r / (2 * t) * eval x P ^ q +
      4 ^ r * t / 2 * eval x P' ^ q) (standardGaussianMeasure n) :=
    ((integrable_eval_pow P q).const_mul _).add ((integrable_eval_pow P' q).const_mul _)
  have hI1 : ∫ x, coordinateEnergy (fun y : Fin n → ℝ => eval y P) x ^ r
        ∂(standardGaussianMeasure n) ≤ 4 ^ r / (2 * t) * M + 4 ^ r * t / 2 * M' := by
    refine (integral_mono hint_ce hint_rhs hpt).trans (le_of_eq ?_)
    rw [integral_add ((integrable_eval_pow P q).const_mul _)
      ((integrable_eval_pow P' q).const_mul _), integral_const_mul, integral_const_mul]
  -- the convexity step
  have hpt2 : ∀ x : Fin n → ℝ, eval x P ^ q ≤ 2 ^ (q - 1) * (|eval x P - m0| ^ q + m0 ^ q) :=
    fun x => by
      have h0 := eval_sqSum_nonneg x L
      have h1 : eval x P ≤ |eval x P - m0| + m0 := by
        have := le_abs_self (eval x P - m0); linarith
      exact (pow_le_pow_left₀ h0 h1 q).trans (add_pow_le (abs_nonneg _) hm0nn q)
  have hint_abs : Integrable (fun x => |eval x P - m0| ^ q) (standardGaussianMeasure n) := by
    have := integrable_abs_pow_eval (P - C m0) q
    simp only [map_sub, eval_C] at this
    exact this
  have hI2 : M ≤ 2 ^ (q - 1) * (∫ x, |eval x P - m0| ^ q ∂(standardGaussianMeasure n) + m0 ^ q) := by
    have hint_r : Integrable (fun x => 2 ^ (q - 1) * (|eval x P - m0| ^ q + m0 ^ q))
        (standardGaussianMeasure n) :=
      (hint_abs.add (integrable_const _)).const_mul _
    refine (integral_mono (integrable_eval_pow P q) hint_r hpt2).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add hint_abs (integrable_const _)]
    simp
  -- arithmetic
  have hM0 : 0 ≤ M := integral_nonneg fun x => pow_nonneg (eval_sqSum_nonneg x L) _
  have hM'0 : 0 ≤ M' := integral_nonneg fun x => pow_nonneg (eval_sqSum_nonneg x (polyDerivs L)) _
  have hI3 : ∫ x, |eval x P - m0| ^ q ∂(standardGaussianMeasure n) ≤
      Kc * (4 ^ r / (2 * t) * M + 4 ^ r * t / 2 * M') :=
    hH2.trans (mul_le_mul_of_nonneg_left hI1 (by positivity))
  have hA0 : (0 : ℝ) ≤ 2 ^ (q - 1) := by positivity
  have hc1 : 2 ^ (q - 1) * (Kc * (4 ^ r / (2 * t))) = w / t := by
    rw [hwdef]; field_simp
  have hc2 : 2 ^ (q - 1) * (Kc * (4 ^ r * t / 2)) = w * t := by
    rw [hwdef]; field_simp
  have hmq : m0 ^ q ≤ μ ^ q := pow_le_pow_left₀ hm0nn hm0μ q
  have hwt : w / t ≤ 1 / 2 := by
    rw [div_le_iff₀ ht0, ht]; linarith
  have hconst : momentStepConst k = 2 * (w * t) := by
    rw [momentStepConst, ← hw, ht]; ring
  have hstep : M ≤ w / t * M + w * t * M' + 2 ^ (q - 1) * μ ^ q := by
    calc M ≤ 2 ^ (q - 1) * (∫ x, |eval x P - m0| ^ q ∂(standardGaussianMeasure n) + m0 ^ q) :=
          hI2
      _ ≤ 2 ^ (q - 1) * (Kc * (4 ^ r / (2 * t) * M + 4 ^ r * t / 2 * M') + μ ^ q) :=
          mul_le_mul_of_nonneg_left (add_le_add hI3 hmq) hA0
      _ = (2 ^ (q - 1) * (Kc * (4 ^ r / (2 * t)))) * M +
          (2 ^ (q - 1) * (Kc * (4 ^ r * t / 2))) * M' + 2 ^ (q - 1) * μ ^ q := by ring
      _ = w / t * M + w * t * M' + 2 ^ (q - 1) * μ ^ q := by rw [hc1, hc2]
  have hwtM : w / t * M ≤ 1 / 2 * M := mul_le_mul_of_nonneg_right hwt hM0
  rw [hconst]
  linarith

end RegularityStructures

end
