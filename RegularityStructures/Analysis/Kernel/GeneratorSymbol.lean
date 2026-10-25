/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.Symbol
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivatives of the symbol kernels under the integral sign

With `C_n(t, b) = ∫ ξ^n e^{-t ξ^{2j}} cos(2π ξ b) dξ` and
`S_n(t, b) = ∫ ξ^n e^{-t ξ^{2j}} sin(2π ξ b) dξ` we have, for `t > 0`,

* `∂_b C_n = -2π S_{n+1}`, `∂_b S_n = 2π C_{n+1}`,
* `∂_t C_n = -C_{n+2j}`.

Since `symKernel j t = C_0(t, ·)`, this gives `k_t'' = -4π² C_2` and `k_t'''' = 16π⁴ C_4`, and hence
the heat equations `∂_t g_t = (4π²)⁻¹ g_t''` and `∂_t k_t = -(16π⁴)⁻¹ k_t''''` (the generator
coefficients of `RegularityStructures.Analysis.Parabolic.Generator`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `C_n(t, b) = ∫ ξ^n exp(-t ξ^{2j}) cos(2π ξ b) dξ`. -/
def symCos (j n : ℕ) (t b : ℝ) : ℝ :=
  ∫ ξ, ξ ^ n * Real.exp (-(t * ξ ^ (2 * j))) * Real.cos (2 * Real.pi * ξ * b)

/-- `S_n(t, b) = ∫ ξ^n exp(-t ξ^{2j}) sin(2π ξ b) dξ`. -/
def symSin (j n : ℕ) (t b : ℝ) : ℝ :=
  ∫ ξ, ξ ^ n * Real.exp (-(t * ξ ^ (2 * j))) * Real.sin (2 * Real.pi * ξ * b)

end RegularityStructures

end

public section

open MeasureTheory Real Filter Topology

namespace RegularityStructures

theorem symKernel_eq_symCos (j : ℕ) (t b : ℝ) : symKernel j t b = symCos j 0 t b := by
  simp [symKernel, symCos]

/-- `|ξ|^n exp(-c ξ^{2j})` is integrable for `c > 0`. -/
theorem integrable_abs_pow_mul_exp {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j) (n : ℕ) :
    Integrable fun ξ : ℝ => |ξ| ^ n * Real.exp (-(c * ξ ^ (2 * j))) := by
  obtain ⟨B₁, h₁⟩ := exists_bound_abs_pow_mul_expPowFun hc hj n
  obtain ⟨B₂, h₂⟩ := exists_bound_abs_pow_mul_expPowFun hc hj (n + 2)
  refine (integrable_inv_one_add_sq.const_mul (B₁ + B₂)).mono' ?_
    (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (by fun_prop : Continuous fun ξ : ℝ =>
      |ξ| ^ n * Real.exp (-(c * ξ ^ (2 * j)))).aestronglyMeasurable
  · have hE : 0 ≤ Real.exp (-(c * ξ ^ (2 * j))) := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg ξ) n) hE)]
    have hsq : (0 : ℝ) < 1 + ξ ^ 2 := by nlinarith [sq_nonneg ξ]
    rw [show (B₁ + B₂) * (1 + ξ ^ 2)⁻¹ = (B₁ + B₂) / (1 + ξ ^ 2) by ring, le_div_iff₀ hsq]
    have e : |ξ| ^ n * Real.exp (-(c * ξ ^ (2 * j))) * (1 + ξ ^ 2) =
        |ξ| ^ n * expPowFun c (2 * j) ξ + |ξ| ^ (n + 2) * expPowFun c (2 * j) ξ := by
      unfold expPowFun
      rw [pow_add, sq_abs]
      ring
    rw [e]
    exact add_le_add (h₁ ξ) (h₂ ξ)

theorem integrable_pow_mul_exp_mul {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j) (n : ℕ)
    {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) :
    Integrable fun ξ : ℝ => ξ ^ n * Real.exp (-(c * ξ ^ (2 * j))) * g ξ := by
  refine (integrable_abs_pow_mul_exp hc hj n).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  calc |ξ| ^ n * Real.exp (-(c * ξ ^ (2 * j))) * |g ξ|
      ≤ |ξ| ^ n * Real.exp (-(c * ξ ^ (2 * j))) * 1 :=
        mul_le_mul_of_nonneg_left (hb ξ)
          (mul_nonneg (pow_nonneg (abs_nonneg ξ) n) (Real.exp_pos _).le)
    _ = _ := mul_one _

theorem hasDerivAt_symCos_b {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j) (n : ℕ) (b : ℝ) :
    HasDerivAt (fun b => symCos j n c b) (-(2 * π) * symSin j (n + 1) c b) b := by
  have hI := integrable_abs_pow_mul_exp hc hj (n + 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := b)
    (s := Set.univ) Filter.univ_mem
    (F := fun b ξ => ξ ^ n * Real.exp (-(c * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * b))
    (F' := fun b ξ => -(2 * π) * (ξ ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j))) *
      Real.sin (2 * π * ξ * b)))
    (bound := fun ξ => 2 * π * (|ξ| ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j)))))
    (Filter.Eventually.of_forall fun x => (by fun_prop : Continuous fun ξ : ℝ =>
      ξ ^ n * Real.exp (-(c * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * x)).aestronglyMeasurable)
    (integrable_pow_mul_exp_mul hc hj n (g := fun ξ => Real.cos (2 * π * ξ * b))
      (by fun_prop) fun x => Real.abs_cos_le_one _)
    (by fun_prop : Continuous fun ξ : ℝ => -(2 * π) * (ξ ^ (n + 1) *
      Real.exp (-(c * ξ ^ (2 * j))) * Real.sin (2 * π * ξ * b))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _),
        abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc |ξ| ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j))) * |Real.sin (2 * π * ξ * x)|
          ≤ |ξ| ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j))) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
              (mul_nonneg (pow_nonneg (abs_nonneg ξ) _) (Real.exp_pos _).le)
        _ = _ := mul_one _)
    (hI.const_mul (2 * π))
    (Filter.Eventually.of_forall fun ξ x _ => by
      have h := (((hasDerivAt_id' x).const_mul (2 * π * ξ)).cos).const_mul
        (ξ ^ n * Real.exp (-(c * ξ ^ (2 * j))))
      convert h using 1
      ring)
  have e : ∫ ξ, -(2 * π) * (ξ ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j))) *
      Real.sin (2 * π * ξ * b)) = -(2 * π) * symSin j (n + 1) c b := by
    rw [integral_const_mul]
    rfl
  rw [e] at key
  exact key.2

theorem hasDerivAt_symSin_b {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j) (n : ℕ) (b : ℝ) :
    HasDerivAt (fun b => symSin j n c b) (2 * π * symCos j (n + 1) c b) b := by
  have hI := integrable_abs_pow_mul_exp hc hj (n + 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := b)
    (s := Set.univ) Filter.univ_mem
    (F := fun b ξ => ξ ^ n * Real.exp (-(c * ξ ^ (2 * j))) * Real.sin (2 * π * ξ * b))
    (F' := fun b ξ => 2 * π * (ξ ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j))) *
      Real.cos (2 * π * ξ * b)))
    (bound := fun ξ => 2 * π * (|ξ| ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j)))))
    (Filter.Eventually.of_forall fun x => (by fun_prop : Continuous fun ξ : ℝ =>
      ξ ^ n * Real.exp (-(c * ξ ^ (2 * j))) * Real.sin (2 * π * ξ * x)).aestronglyMeasurable)
    (integrable_pow_mul_exp_mul hc hj n (g := fun ξ => Real.sin (2 * π * ξ * b))
      (by fun_prop) fun x => Real.abs_sin_le_one _)
    (by fun_prop : Continuous fun ξ : ℝ => 2 * π * (ξ ^ (n + 1) *
      Real.exp (-(c * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * b))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_mul,
        abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc |ξ| ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j))) * |Real.cos (2 * π * ξ * x)|
          ≤ |ξ| ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j))) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
              (mul_nonneg (pow_nonneg (abs_nonneg ξ) _) (Real.exp_pos _).le)
        _ = _ := mul_one _)
    (hI.const_mul (2 * π))
    (Filter.Eventually.of_forall fun ξ x _ => by
      have h := (((hasDerivAt_id' x).const_mul (2 * π * ξ)).sin).const_mul
        (ξ ^ n * Real.exp (-(c * ξ ^ (2 * j))))
      convert h using 1
      ring)
  have e : ∫ ξ, 2 * π * (ξ ^ (n + 1) * Real.exp (-(c * ξ ^ (2 * j))) *
      Real.cos (2 * π * ξ * b)) = 2 * π * symCos j (n + 1) c b := by
    rw [integral_const_mul]
    rfl
  rw [e] at key
  exact key.2

theorem hasDerivAt_symCos_t {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : 0 < j) (n : ℕ) (b : ℝ) :
    HasDerivAt (fun s => symCos j n s b) (-symCos j (n + 2 * j) t b) t := by
  have hI := integrable_abs_pow_mul_exp (half_pos ht) hj (n + 2 * j)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t)
    (s := Set.Ioi (t / 2)) (Ioi_mem_nhds (half_lt_self ht))
    (F := fun s ξ => ξ ^ n * Real.exp (-(s * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * b))
    (F' := fun s ξ => -(ξ ^ (n + 2 * j) * Real.exp (-(s * ξ ^ (2 * j))) *
      Real.cos (2 * π * ξ * b)))
    (bound := fun ξ => |ξ| ^ (n + 2 * j) * Real.exp (-(t / 2 * ξ ^ (2 * j))))
    (Filter.Eventually.of_forall fun x => (by fun_prop : Continuous fun ξ : ℝ =>
      ξ ^ n * Real.exp (-(x * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * b)).aestronglyMeasurable)
    (integrable_pow_mul_exp_mul ht hj n (g := fun ξ => Real.cos (2 * π * ξ * b))
      (by fun_prop) fun x => Real.abs_cos_le_one _)
    (by fun_prop : Continuous fun ξ : ℝ => -(ξ ^ (n + 2 * j) * Real.exp (-(t * ξ ^ (2 * j))) *
      Real.cos (2 * π * ξ * b))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ x hx => by
      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      have hxi : 0 ≤ ξ ^ (2 * j) := Even.pow_nonneg ⟨j, by ring⟩ ξ
      have hexp : Real.exp (-(x * ξ ^ (2 * j))) ≤ Real.exp (-(t / 2 * ξ ^ (2 * j))) :=
        Real.exp_le_exp.2 (by
          have : t / 2 * ξ ^ (2 * j) ≤ x * ξ ^ (2 * j) :=
            mul_le_mul_of_nonneg_right (le_of_lt hx) hxi
          linarith)
      calc |ξ| ^ (n + 2 * j) * Real.exp (-(x * ξ ^ (2 * j))) * |Real.cos (2 * π * ξ * b)|
          ≤ |ξ| ^ (n + 2 * j) * Real.exp (-(x * ξ ^ (2 * j))) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
              (mul_nonneg (pow_nonneg (abs_nonneg ξ) _) (Real.exp_pos _).le)
        _ = |ξ| ^ (n + 2 * j) * Real.exp (-(x * ξ ^ (2 * j))) := mul_one _
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (pow_nonneg (abs_nonneg ξ) _))
    hI
    (Filter.Eventually.of_forall fun ξ x _ => by
      have h1 := ((hasDerivAt_id' x).mul_const (ξ ^ (2 * j))).neg.exp
      have h := (h1.const_mul (ξ ^ n)).mul_const (Real.cos (2 * π * ξ * b))
      convert h using 1
      simp only [Pi.neg_apply]
      rw [pow_add]
      ring)
  have e : ∫ ξ, -(ξ ^ (n + 2 * j) * Real.exp (-(t * ξ ^ (2 * j))) *
      Real.cos (2 * π * ξ * b)) = -symCos j (n + 2 * j) t b := by
    rw [integral_neg]
    rfl
  rw [e] at key
  exact key.2

end RegularityStructures

end
