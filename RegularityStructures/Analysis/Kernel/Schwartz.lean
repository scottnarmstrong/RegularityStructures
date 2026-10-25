/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The Schwartz functions `ξ ↦ exp(-c ξ^{2j})`

For `c > 0` and `j ≥ 1` the function `ξ ↦ exp(-c ξ^{2j})` is a Schwartz function. The `n`-th
derivative is `p_n(ξ) exp(-c ξ^{2j})` for the polynomials `p_0 = 1`,
`p_{n+1} = p_n' - 2jc X^{2j-1} p_n`, and `|ξ|^k exp(-c ξ^{2j})` is bounded.

This is the symbol of the auxiliary kernels `Q_t` of the regularising semigroup
(`RegularityStructures.Analysis.Kernel.Symbol`), with `j = 1` for the heat kernel and `j = 2` for
the quartic kernel `exp(-t ξ⁴)`; see [Hos25, Example 2.7] (arXiv:2310.07396v2).
-/

@[expose] public noncomputable section

open Polynomial SchwartzMap

namespace RegularityStructures

/-- The real function `ξ ↦ exp(-c ξ^m)`. -/
def expPowFun (c : ℝ) (m : ℕ) (x : ℝ) : ℝ := Real.exp (-(c * x ^ m))

/-- The polynomials `p_n` with `(d/dξ)^n exp(-c ξ^m) = p_n(ξ) exp(-c ξ^m)`. -/
def expPowPoly (c : ℝ) (m : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => derivative (expPowPoly c m n) - C (c * m) * X ^ (m - 1) * expPowPoly c m n

/-- The complex-valued `n`-th derivative `p_n(ξ) exp(-c ξ^m)`. -/
def expPowDeriv (c : ℝ) (m n : ℕ) (x : ℝ) : ℂ :=
  (((expPowPoly c m n).eval x * expPowFun c m x : ℝ) : ℂ)

end RegularityStructures

end

public section

open Polynomial SchwartzMap

namespace RegularityStructures

theorem hasDerivAt_expPowFun (c : ℝ) (m : ℕ) (x : ℝ) :
    HasDerivAt (expPowFun c m) (-(c * m * x ^ (m - 1)) * expPowFun c m x) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(c * x ^ m)) (-(c * (m * x ^ (m - 1)))) x :=
    ((hasDerivAt_pow m x).const_mul c).neg
  have := h1.exp
  unfold expPowFun
  convert this using 1
  ring

theorem hasDerivAt_expPowDeriv (c : ℝ) (m n : ℕ) (x : ℝ) :
    HasDerivAt (expPowDeriv c m n) (expPowDeriv c m (n + 1) x) x := by
  have h1 : HasDerivAt (fun x => (expPowPoly c m n).eval x * expPowFun c m x)
      ((expPowPoly c m (n + 1)).eval x * expPowFun c m x) x := by
    have := (Polynomial.hasDerivAt (expPowPoly c m n) x).mul (hasDerivAt_expPowFun c m x)
    convert this using 1
    simp only [expPowPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    ring
  exact h1.ofReal_comp

theorem iteratedDeriv_expPowDeriv (c : ℝ) (m n k : ℕ) :
    iteratedDeriv k (expPowDeriv c m n) = expPowDeriv c m (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have hd : deriv (expPowDeriv c m n) = expPowDeriv c m (n + 1) :=
      funext fun x => (hasDerivAt_expPowDeriv c m n x).deriv
    rw [iteratedDeriv_succ', hd, ih, show n + 1 + k = n + (k + 1) by omega]

theorem iteratedDeriv_expPowDeriv_zero (c : ℝ) (m n : ℕ) :
    iteratedDeriv n (expPowDeriv c m 0) = expPowDeriv c m n := by
  simpa using iteratedDeriv_expPowDeriv c m 0 n

/-- Growth bound: `|x|^k exp(-c x^{2j})` is bounded. -/
theorem exists_bound_abs_pow_mul_expPowFun {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j) (k : ℕ) :
    ∃ B : ℝ, ∀ x : ℝ, |x| ^ k * expPowFun c (2 * j) x ≤ B := by
  refine ⟨1 + k.factorial / c ^ k, fun x => ?_⟩
  have hE : expPowFun c (2 * j) x = Real.exp (-(c * |x| ^ (2 * j))) := by
    rw [expPowFun, Even.pow_abs (even_two_mul j)]
  have hy : 0 ≤ |x| := abs_nonneg x
  set y := |x| with hydef
  set u := c * y ^ (2 * j) with hu
  have hu0 : 0 ≤ u := by positivity
  have hexp : u ^ k * Real.exp (-u) ≤ k.factorial := by
    have := Real.pow_div_factorial_le_exp u hu0 k
    have hpos := Real.exp_pos u
    have h2 : u ^ k ≤ k.factorial * Real.exp u := by
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    calc u ^ k * Real.exp (-u) ≤ (k.factorial * Real.exp u) * Real.exp (-u) := by gcongr
      _ = k.factorial := by rw [mul_assoc, ← Real.exp_add]; simp
  have hyk : y ^ k ≤ 1 + y ^ (2 * j * k) := by
    rcases le_total y 1 with h | h
    · linarith [pow_le_one₀ hy h (n := k), pow_nonneg hy (2 * j * k)]
    · have : y ^ k ≤ y ^ (2 * j * k) :=
        pow_le_pow_right₀ h (by nlinarith [Nat.mul_le_mul_right k (show 1 ≤ 2 * j by omega)])
      linarith
  have hyu : y ^ (2 * j * k) * Real.exp (-u) ≤ k.factorial / c ^ k := by
    have : y ^ (2 * j * k) = u ^ k / c ^ k := by
      rw [hu, mul_pow, ← pow_mul, mul_div_cancel_left₀ _ (by positivity)]
    rw [this, div_mul_eq_mul_div]
    gcongr
  have hE1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [hE]
  calc y ^ k * Real.exp (-u) ≤ (1 + y ^ (2 * j * k)) * Real.exp (-u) := by gcongr
    _ = Real.exp (-u) + y ^ (2 * j * k) * Real.exp (-u) := by ring
    _ ≤ 1 + k.factorial / c ^ k := by linarith

/-- Polynomial growth bound: `|x|^k |p(x)| exp(-c x^{2j})` is bounded. -/
theorem exists_bound_abs_pow_mul_eval_mul_expPowFun {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j)
    (p : ℝ[X]) (k : ℕ) :
    ∃ B : ℝ, ∀ x : ℝ, |x| ^ k * (|p.eval x| * expPowFun c (2 * j) x) ≤ B := by
  choose B hB using fun i : ℕ => exists_bound_abs_pow_mul_expPowFun hc hj (k + i)
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * B i, fun x => ?_⟩
  have hE : 0 ≤ expPowFun c (2 * j) x := (Real.exp_pos _).le
  have h1 : |p.eval x| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i := by
    rw [eval_eq_sum_range]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_pow]
  calc |x| ^ k * (|p.eval x| * expPowFun c (2 * j) x)
      ≤ |x| ^ k * ((∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i) *
        expPowFun c (2 * j) x) := by gcongr
    _ = ∑ i ∈ Finset.range (p.natDegree + 1),
          |p.coeff i| * (|x| ^ (k + i) * expPowFun c (2 * j) x) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_add]; ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => by gcongr; exact hB i x

open scoped ContDiff in
/-- The Schwartz function `ξ ↦ exp(-c ξ^{2j})` (`c > 0`, `j ≥ 1`), complex valued. -/
@[expose] noncomputable def expPowSchwartz {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j) : 𝓢(ℝ, ℂ) where
  toFun x := (expPowFun c (2 * j) x : ℂ)
  smooth' := by
    have : ContDiff ℝ ∞ (expPowFun c (2 * j)) := by
      unfold expPowFun
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp this
  decay' k n := by
    obtain ⟨B, hB⟩ := exists_bound_abs_pow_mul_eval_mul_expPowFun hc hj
      (expPowPoly c (2 * j) n) k
    refine ⟨B, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have : iteratedDeriv n (fun x : ℝ => (expPowFun c (2 * j) x : ℂ)) x =
        expPowDeriv c (2 * j) n x := by
      have h0 : expPowDeriv c (2 * j) 0 = fun x => (expPowFun c (2 * j) x : ℂ) := by
        funext x
        simp [expPowDeriv, expPowPoly]
      rw [← h0, iteratedDeriv_expPowDeriv_zero]
    rw [this]
    have hE : 0 ≤ expPowFun c (2 * j) x := (Real.exp_pos _).le
    simpa [expPowDeriv, abs_mul, abs_of_nonneg hE] using hB x

@[simp]
theorem expPowSchwartz_apply {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j) (x : ℝ) :
    expPowSchwartz hc hj x = (Real.exp (-(c * x ^ (2 * j))) : ℝ) := rfl

end RegularityStructures

end
