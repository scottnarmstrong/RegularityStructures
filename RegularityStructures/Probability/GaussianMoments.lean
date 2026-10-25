/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Moments of centred real Gaussian variables

For `v ≥ 0` the centred real Gaussian law `gaussianReal 0 v` has

* `∫ x² = v`, `∫ x⁴ = 3 v²` and `∫ x⁶ = 15 v³`;
* `∫ x^(2k+1) = 0`.

The even moments are the derivatives at `0` of the moment generating function
`t ↦ exp (v t² / 2)` (`ProbabilityTheory.iteratedDeriv_mgf_zero`). Each derivative is
`P_k(t) exp (v t² / 2)` for an explicit polynomial `P_k`, with `P_{k+1} = P_k' + v t P_k`.

The second part transfers these identities to a real random variable `Y` with a Gaussian law and
mean zero: `E[Y⁴] = 3 E[Y²]²` and `E[Y⁶] = 15 E[Y²]³`. These are the scalar inputs of the
Isserlis–Wick formulas in `RegularityStructures.Probability.Isserlis`.
-/

public section

open MeasureTheory ProbabilityTheory Real Polynomial
open scoped NNReal

namespace RegularityStructures

/-! ### Derivatives of `exp (v t² / 2)` -/

section GaussExp

variable (v : ℝ)

/-- One differentiation step: `(p e)' = (p' + v t p) e` for `e(t) = exp (v t² / 2)`. -/
theorem hasDerivAt_mul_exp_half_sq {p : ℝ → ℝ} {p' t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun s => p s * rexp (v * s ^ 2 / 2))
      ((p' + p t * (v * t)) * rexp (v * t ^ 2 / 2)) t := by
  have he : HasDerivAt (fun s => rexp (v * s ^ 2 / 2)) (rexp (v * t ^ 2 / 2) * (v * t)) t := by
    have := (((hasDerivAt_pow 2 t).const_mul v).div_const 2).exp
    convert this using 1
    push_cast
    ring
  convert hp.mul he using 1
  ring

/-- If the `n`-th derivative of `f` is `P(t) exp (v t² / 2)` and `P' + v t P = Q`, then the
`(n+1)`-th derivative is `Q(t) exp (v t² / 2)`. -/
theorem iteratedDeriv_succ_eq_eval_mul_exp {n : ℕ} {f : ℝ → ℝ} {P Q : ℝ[X]}
    (hn : iteratedDeriv n f = fun t => P.eval t * rexp (v * t ^ 2 / 2))
    (hQ : ∀ t, (derivative P).eval t + P.eval t * (v * t) = Q.eval t) :
    iteratedDeriv (n + 1) f = fun t => Q.eval t * rexp (v * t ^ 2 / 2) := by
  rw [iteratedDeriv_succ, hn]
  funext t
  rw [(hasDerivAt_mul_exp_half_sq v (P.hasDerivAt t)).deriv, hQ]

/-- The first six derivatives of `t ↦ exp (v t² / 2)`, in closed form. -/
theorem iteratedDeriv_exp_half_sq :
    iteratedDeriv 2 (fun t => rexp (v * t ^ 2 / 2)) =
        (fun t => (v + v ^ 2 * t ^ 2) * rexp (v * t ^ 2 / 2)) ∧
      iteratedDeriv 4 (fun t => rexp (v * t ^ 2 / 2)) =
        (fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * rexp (v * t ^ 2 / 2)) ∧
      iteratedDeriv 6 (fun t => rexp (v * t ^ 2 / 2)) =
        fun t => (15 * v ^ 3 + 45 * v ^ 4 * t ^ 2 + 15 * v ^ 5 * t ^ 4 + v ^ 6 * t ^ 6) *
          rexp (v * t ^ 2 / 2) := by
  have h0 : iteratedDeriv 0 (fun t => rexp (v * t ^ 2 / 2)) =
      fun t => (C 1 : ℝ[X]).eval t * rexp (v * t ^ 2 / 2) := by
    simp
  have h1 := iteratedDeriv_succ_eq_eval_mul_exp v h0 (Q := C v * X) (fun t => by simp)
  have h2 := iteratedDeriv_succ_eq_eval_mul_exp v h1 (Q := C v + C (v ^ 2) * X ^ 2)
    (fun t => by simp; ring)
  have h3 := iteratedDeriv_succ_eq_eval_mul_exp v h2
    (Q := C (3 * v ^ 2) * X + C (v ^ 3) * X ^ 3) (fun t => by simp [derivative_pow]; ring)
  have h4 := iteratedDeriv_succ_eq_eval_mul_exp v h3
    (Q := C (3 * v ^ 2) + C (6 * v ^ 3) * X ^ 2 + C (v ^ 4) * X ^ 4)
    (fun t => by simp [derivative_pow]; ring)
  have h5 := iteratedDeriv_succ_eq_eval_mul_exp v h4
    (Q := C (15 * v ^ 3) * X + C (10 * v ^ 4) * X ^ 3 + C (v ^ 5) * X ^ 5)
    (fun t => by simp [derivative_pow]; ring)
  have h6 := iteratedDeriv_succ_eq_eval_mul_exp v h5
    (Q := C (15 * v ^ 3) + C (45 * v ^ 4) * X ^ 2 + C (15 * v ^ 5) * X ^ 4 + C (v ^ 6) * X ^ 6)
    (fun t => by simp [derivative_pow]; ring)
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]
    funext t
    simp
  · rw [h4]
    funext t
    simp
  · rw [h6]
    funext t
    simp

end GaussExp

/-! ### Moments of `gaussianReal 0 v` -/

section GaussianReal

variable (v : ℝ≥0)

/-- Every power of the identity is integrable for a real Gaussian law. -/
theorem integrable_pow_gaussianReal (μ : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal μ v) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) k

/-- The moments of `gaussianReal 0 v` are the derivatives at zero of `t ↦ exp (v t² / 2)`. -/
theorem integral_pow_gaussianReal_eq_iteratedDeriv (k : ℕ) :
    ∫ x, x ^ k ∂gaussianReal 0 v = iteratedDeriv k (fun t => rexp (v * t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) k
  rw [mgf_fun_id_gaussianReal] at h
  simp only [zero_mul, zero_add] at h
  rw [h]
  simp

theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  rw [integral_pow_gaussianReal_eq_iteratedDeriv, (iteratedDeriv_exp_half_sq v).1]
  simp

theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  rw [integral_pow_gaussianReal_eq_iteratedDeriv, (iteratedDeriv_exp_half_sq v).2.1]
  simp

end GaussianReal

/-! ### Centred real Gaussian random variables -/

end RegularityStructures

namespace ProbabilityTheory.HasGaussianLaw

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}

/-- The law of a centred real Gaussian variable is `gaussianReal 0 v` with `v = Var[Y]`. -/
theorem map_eq_gaussianReal_of_integral_eq_zero (hY : HasGaussianLaw Y P)
    (h0 : ∫ ω, Y ω ∂P = 0) :
    P.map Y = gaussianReal 0 (Var[Y; P]).toNNReal := by
  rw [hY.map_eq_gaussianReal, h0]

/-- A real Gaussian variable has finite moments of every order. -/
theorem integrable_pow (hY : HasGaussianLaw Y P) (k : ℕ) :
    Integrable (fun ω => Y ω ^ k) P := by
  have h := integrable_pow_gaussianReal (Var[Y; P]).toNNReal (∫ ω, Y ω ∂P) k
  rw [← hY.map_eq_gaussianReal] at h
  exact (integrable_map_measure (continuous_pow k).aestronglyMeasurable hY.aemeasurable).mp h

/-- For a centred real Gaussian variable, every moment is the corresponding moment of
`gaussianReal 0 v`. -/
theorem integral_pow_eq (hY : HasGaussianLaw Y P) (h0 : ∫ ω, Y ω ∂P = 0) (k : ℕ) :
    ∫ ω, Y ω ^ k ∂P = ∫ x, x ^ k ∂gaussianReal 0 (Var[Y; P]).toNNReal := by
  rw [← hY.map_eq_gaussianReal_of_integral_eq_zero h0,
    integral_map hY.aemeasurable (continuous_pow k).aestronglyMeasurable]

theorem integral_sq_eq (hY : HasGaussianLaw Y P) (h0 : ∫ ω, Y ω ∂P = 0) :
    ∫ ω, Y ω ^ 2 ∂P = (Var[Y; P]).toNNReal := by
  rw [hY.integral_pow_eq h0, integral_sq_gaussianReal]

/-- **Fourth moment of a centred Gaussian.** `E[Y⁴] = 3 E[Y²]²`. -/
theorem integral_pow_four (hY : HasGaussianLaw Y P) (h0 : ∫ ω, Y ω ∂P = 0) :
    ∫ ω, Y ω ^ 4 ∂P = 3 * (∫ ω, Y ω ^ 2 ∂P) ^ 2 := by
  rw [hY.integral_sq_eq h0, hY.integral_pow_eq h0, integral_pow_four_gaussianReal]

end ProbabilityTheory.HasGaussianLaw

end
