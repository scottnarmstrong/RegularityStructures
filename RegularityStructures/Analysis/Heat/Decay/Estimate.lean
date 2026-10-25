/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decay.Poly
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Elementary estimates for Gaussian-type expressions

* `IsGaussPoly.exists_bound`: a polynomial expression in `t⁻¹, x` is bounded by
  `C (1 + t⁻¹)^a (1 + |x|²)^a` on `{t > 0}`.
* `exists_bound_pow_mul_exp_neg`: for `w ≥ w₀ > 0`, `r ≥ 1`:
  `(1 + w)^n (1 + r)^b r^m exp(-(r w / 4)) ≤ C`.
* `gaussKernel_le`: `(4π t)^{-3/2} ≤ (1 + t⁻¹)²`.
-/

public section

namespace RegularityStructures

theorem IsGaussPoly.exists_bound {f : ParabolicSpace → ℝ} (hf : IsGaussPoly f) :
    ∃ (a : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ParabolicSpace, 0 < z.1 →
      |f z| ≤ C * ((1 + z.1⁻¹) ^ a * (1 + sqNorm3 z.2) ^ a) := by
  induction hf with
  | const c => exact ⟨0, |c|, abs_nonneg _, fun z _ => by simp⟩
  | invT =>
    refine ⟨1, 1, zero_le_one, fun z hz => ?_⟩
    have hs : 0 ≤ sqNorm3 z.2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hi : 0 ≤ z.1⁻¹ := inv_nonneg.2 hz.le
    rw [abs_of_nonneg hi]
    simp only [pow_one, one_mul]
    nlinarith
  | coord i =>
    refine ⟨1, 1, zero_le_one, fun z hz => ?_⟩
    have hs : z.2 i ^ 2 ≤ sqNorm3 z.2 :=
      Finset.single_le_sum (f := fun j => z.2 j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hi : 0 ≤ z.1⁻¹ := inv_nonneg.2 hz.le
    have h1 : |z.2 i| ≤ 1 + z.2 i ^ 2 := by
      rcases abs_cases (z.2 i) with ⟨h, _⟩ | ⟨h, _⟩ <;> nlinarith [sq_nonneg (z.2 i - 1),
        sq_nonneg (z.2 i + 1)]
    simp only [pow_one, one_mul]
    nlinarith
  | @add f g hf hg ihf ihg =>
    obtain ⟨a, C, hC, h1⟩ := ihf
    obtain ⟨b, D, hD, h2⟩ := ihg
    refine ⟨max a b, C + D, add_nonneg hC hD, fun z hz => ?_⟩
    have hs : 0 ≤ sqNorm3 z.2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hi : 0 ≤ z.1⁻¹ := inv_nonneg.2 hz.le
    have hu : (1 : ℝ) ≤ 1 + z.1⁻¹ := by linarith
    have hv : (1 : ℝ) ≤ 1 + sqNorm3 z.2 := by linarith
    have ha : (1 + z.1⁻¹) ^ a * (1 + sqNorm3 z.2) ^ a ≤
        (1 + z.1⁻¹) ^ max a b * (1 + sqNorm3 z.2) ^ max a b :=
      mul_le_mul (pow_le_pow_right₀ hu (le_max_left _ _)) (pow_le_pow_right₀ hv (le_max_left _ _))
        (by positivity) (by positivity)
    have hb : (1 + z.1⁻¹) ^ b * (1 + sqNorm3 z.2) ^ b ≤
        (1 + z.1⁻¹) ^ max a b * (1 + sqNorm3 z.2) ^ max a b :=
      mul_le_mul (pow_le_pow_right₀ hu (le_max_right _ _)) (pow_le_pow_right₀ hv (le_max_right _ _))
        (by positivity) (by positivity)
    calc |f z + g z| ≤ |f z| + |g z| := abs_add_le _ _
      _ ≤ C * ((1 + z.1⁻¹) ^ a * (1 + sqNorm3 z.2) ^ a) +
          D * ((1 + z.1⁻¹) ^ b * (1 + sqNorm3 z.2) ^ b) := add_le_add (h1 z hz) (h2 z hz)
      _ ≤ C * ((1 + z.1⁻¹) ^ max a b * (1 + sqNorm3 z.2) ^ max a b) +
          D * ((1 + z.1⁻¹) ^ max a b * (1 + sqNorm3 z.2) ^ max a b) :=
        add_le_add (mul_le_mul_of_nonneg_left ha hC) (mul_le_mul_of_nonneg_left hb hD)
      _ = (C + D) * ((1 + z.1⁻¹) ^ max a b * (1 + sqNorm3 z.2) ^ max a b) := by ring
  | @mul f g hf hg ihf ihg =>
    obtain ⟨a, C, hC, h1⟩ := ihf
    obtain ⟨b, D, hD, h2⟩ := ihg
    refine ⟨a + b, C * D, mul_nonneg hC hD, fun z hz => ?_⟩
    rw [abs_mul]
    calc |f z| * |g z| ≤ (C * ((1 + z.1⁻¹) ^ a * (1 + sqNorm3 z.2) ^ a)) *
          (D * ((1 + z.1⁻¹) ^ b * (1 + sqNorm3 z.2) ^ b)) :=
        mul_le_mul (h1 z hz) (h2 z hz) (abs_nonneg _) (mul_nonneg hC (by
          have hs : 0 ≤ sqNorm3 z.2 := Finset.sum_nonneg fun i _ => sq_nonneg _
          have hi : 0 ≤ z.1⁻¹ := inv_nonneg.2 hz.le
          positivity))
      _ = C * D * ((1 + z.1⁻¹) ^ (a + b) * (1 + sqNorm3 z.2) ^ (a + b)) := by
        rw [pow_add, pow_add]
        ring

theorem pow_mul_exp_neg_le {v : ℝ} (hv : 0 ≤ v) (N : ℕ) :
    v ^ N * Real.exp (-v) ≤ N.factorial := by
  have h := Real.pow_div_factorial_le_exp v hv N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf] at h
  have h2 : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  have he : 0 < Real.exp (-v) := Real.exp_pos _
  calc v ^ N * Real.exp (-v) ≤ (Real.exp v * N.factorial) * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right h he.le
    _ = N.factorial := by rw [mul_right_comm, h2, one_mul]

/-- Algebraic core: polynomial growth in `w` and `r` is beaten by `exp(-(r w / 4))`. -/
private theorem poly_le_mul_pow {n b m : ℕ} {w₀ w r : ℝ} (hw₀ : 0 < w₀) (hw : w₀ ≤ w) (hr : 1 ≤ r) :
    (1 + w) ^ n * (1 + r) ^ b * r ^ m ≤
      ((1 + w₀⁻¹) * 4) ^ n * 2 ^ b * (4 / w₀) ^ (b + m) * (r * w / 4) ^ (n + b + m) := by
  have hwpos : 0 < w := hw₀.trans_le hw
  set v := r * w / 4 with hv
  have h1 : 1 + w ≤ ((1 + w₀⁻¹) * 4) * v := by
    have e1 : 1 ≤ w / w₀ := by rw [le_div_iff₀ hw₀]; linarith
    have e2 : 1 + w ≤ (1 + w₀⁻¹) * w := by
      have : w₀⁻¹ * w = w / w₀ := by field_simp
      nlinarith
    have e3 : w ≤ 4 * v := by rw [hv]; nlinarith
    calc 1 + w ≤ (1 + w₀⁻¹) * w := e2
      _ ≤ (1 + w₀⁻¹) * (4 * v) := mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = ((1 + w₀⁻¹) * 4) * v := by ring
  have h2 : 1 + r ≤ 2 * r := by linarith
  have h3 : r ≤ (4 / w₀) * v := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hw₀, hv]
    nlinarith
  have hr0 : 0 ≤ r := by linarith
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  calc (1 + w) ^ n * (1 + r) ^ b * r ^ m
      ≤ (((1 + w₀⁻¹) * 4) * v) ^ n * (2 * r) ^ b * ((4 / w₀) * v) ^ m := by
        gcongr
    _ ≤ (((1 + w₀⁻¹) * 4) * v) ^ n * (2 * ((4 / w₀) * v)) ^ b * ((4 / w₀) * v) ^ m := by
        gcongr
    _ = ((1 + w₀⁻¹) * 4) ^ n * 2 ^ b * (4 / w₀) ^ (b + m) * v ^ (n + b + m) := by
        rw [mul_pow ((1 + w₀⁻¹) * 4) v n, mul_pow 2 ((4 / w₀) * v) b, mul_pow (4 / w₀) v b,
          mul_pow (4 / w₀) v m, pow_add (4 / w₀) b m, pow_add v (n + b) m, pow_add v n b]
        ring

theorem exists_bound_pow_mul_exp_neg (n b m : ℕ) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w r : ℝ, w₀ ≤ w → 1 ≤ r →
      (1 + w) ^ n * (1 + r) ^ b * r ^ m * Real.exp (-(r * w / 4)) ≤ C := by
  refine ⟨((1 + w₀⁻¹) * 4) ^ n * 2 ^ b * (4 / w₀) ^ (b + m) * (n + b + m).factorial,
    by positivity, fun w r hw hr => ?_⟩
  have hwpos : 0 < w := hw₀.trans_le hw
  have hv0 : 0 ≤ r * w / 4 := by
    have : 0 ≤ r := by linarith
    positivity
  have h := poly_le_mul_pow (n := n) (b := b) (m := m) hw₀ hw hr
  have he := Real.exp_pos (-(r * w / 4))
  calc (1 + w) ^ n * (1 + r) ^ b * r ^ m * Real.exp (-(r * w / 4))
      ≤ (((1 + w₀⁻¹) * 4) ^ n * 2 ^ b * (4 / w₀) ^ (b + m) * (r * w / 4) ^ (n + b + m)) *
          Real.exp (-(r * w / 4)) := mul_le_mul_of_nonneg_right h he.le
    _ = ((1 + w₀⁻¹) * 4) ^ n * 2 ^ b * (4 / w₀) ^ (b + m) *
          ((r * w / 4) ^ (n + b + m) * Real.exp (-(r * w / 4))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le hv0 _) (by positivity)

/-- `(4π t)^{-3/2} ≤ (1 + t⁻¹)²` for `t > 0`. -/
theorem rpow_neg_three_halves_le {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) ≤ (1 + t⁻¹) ^ 2 := by
  set y := 4 * Real.pi * t with hy
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have hypos : 0 < y := by rw [hy]; positivity
  have hyi : y⁻¹ ≤ t⁻¹ := by
    rw [hy]
    apply inv_anti₀ ht
    nlinarith
  have hq : 0 < y ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hypos _
  have hq2 : (y ^ (-(1 : ℝ) / 2)) ^ 2 = y⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hypos.le, ← Real.rpow_neg_one]
    norm_num
  have hsplit : y ^ (-(3 : ℝ) / 2) = y⁻¹ * y ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hypos]
    norm_num
  have hqle : y ^ (-(1 : ℝ) / 2) ≤ 1 + y⁻¹ := by
    nlinarith [sq_nonneg (y ^ (-(1 : ℝ) / 2) - 1), inv_pos.2 hypos]
  have hit : 0 < t⁻¹ := inv_pos.2 ht
  have hyi0 : 0 < y⁻¹ := inv_pos.2 hypos
  rw [hsplit]
  calc y⁻¹ * y ^ (-(1 : ℝ) / 2) ≤ y⁻¹ * (1 + y⁻¹) := mul_le_mul_of_nonneg_left hqle hyi0.le
    _ ≤ t⁻¹ * (1 + t⁻¹) := mul_le_mul hyi (by linarith) (by linarith) hit.le
    _ ≤ (1 + t⁻¹) ^ 2 := by nlinarith

end RegularityStructures

end
