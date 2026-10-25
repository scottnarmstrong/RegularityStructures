/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# One-dimensional brackets at a length scale

`blockBracket n l u = (1 + |u| / l) ^ (-n)` is the Japanese bracket at length `l`. We prove the
elementary comparisons used for the block envelope of the parabolic kernel
(`RegularityStructures.Analysis.Kernel.BlockEnvelope.Envelope`): the weighted bound
`|u|^p (1 + |u|/l)^{-n} ≤ l^p (1 + |u|/l)^{-(n-p)}`, the Peetre inequality, and the comparison of
the scaled profiles `r^{-θ} f (r^{-θ} b)` for `r ∈ [s, 3s]` with the profile at `s`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The bracket `(1 + |u| / l)^{-n}` at length scale `l`. -/
def blockBracket (n : ℝ) (l u : ℝ) : ℝ := (1 + |u| / l) ^ (-n)

end RegularityStructures

end

public section

namespace RegularityStructures

theorem blockBracket_pos (n : ℝ) {l : ℝ} (hl : 0 < l) (u : ℝ) : 0 < blockBracket n l u :=
  Real.rpow_pos_of_pos (by have := div_nonneg (abs_nonneg u) hl.le; linarith) _

theorem blockBracket_nonneg (n : ℝ) {l : ℝ} (hl : 0 < l) (u : ℝ) : 0 ≤ blockBracket n l u :=
  (blockBracket_pos n hl u).le

/-- `|u|^p (1 + |u|/l)^{-n} ≤ l^p (1 + |u|/l)^{-(n-p)}`. -/
theorem blockBracket_mul_rpow_le (n : ℝ) {l : ℝ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p) (u : ℝ) :
    blockBracket n l u * |u| ^ p ≤ l ^ p * blockBracket (n - p) l u := by
  have hx : 0 ≤ |u| / l := div_nonneg (abs_nonneg u) hl.le
  have h1 : 0 < 1 + |u| / l := by linarith
  have habs : |u| = l * (|u| / l) := by field_simp
  have h2 : |u| ^ p ≤ l ^ p * (1 + |u| / l) ^ p := by
    rw [← Real.mul_rpow hl.le h1.le]
    refine Real.rpow_le_rpow (abs_nonneg u) ?_ hp
    rw [mul_add, mul_one, ← habs]
    linarith
  have h3 : blockBracket (n - p) l u = blockBracket n l u * (1 + |u| / l) ^ p := by
    unfold blockBracket
    rw [show -(n - p) = -n + p by ring, Real.rpow_add h1]
  rw [h3]
  have h4 := blockBracket_nonneg n hl u
  calc blockBracket n l u * |u| ^ p ≤ blockBracket n l u * (l ^ p * (1 + |u| / l) ^ p) :=
        mul_le_mul_of_nonneg_left h2 h4
    _ = _ := by ring

/-- Peetre: `(1 + |v|/l)^{-n} ≤ 2^n (1 + |u|/l)^{-n}` when `|u - v| ≤ l`. -/
theorem blockBracket_le_two_pow_mul (n : ℕ) {l : ℝ} (hl : 0 < l) {u v : ℝ} (h : |u - v| ≤ l) :
    blockBracket n l v ≤ 2 ^ n * blockBracket n l u := by
  have hu : 0 ≤ |u| / l := div_nonneg (abs_nonneg u) hl.le
  have hv : 0 ≤ |v| / l := div_nonneg (abs_nonneg v) hl.le
  have hy : 0 < 1 + |u| / l := by linarith
  have hx : 0 < 1 + |v| / l := by linarith
  have habs : |u| ≤ |v| + l := by
    have := abs_sub_abs_le_abs_sub u v
    linarith
  have hyx : 1 + |u| / l ≤ 2 * (1 + |v| / l) := by
    have h1 : |u| / l ≤ |v| / l + 1 := by
      rw [div_le_iff₀ hl]
      have : (|v| / l + 1) * l = |v| + l := by field_simp
      linarith
    linarith
  have hpow : (1 + |u| / l) ^ n ≤ (2 * (1 + |v| / l)) ^ n := pow_le_pow_left₀ hy.le hyx n
  unfold blockBracket
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le, Real.rpow_natCast, Real.rpow_natCast]
  have h2 : ((1 + |v| / l) ^ n)⁻¹ = 2 ^ n * ((2 * (1 + |v| / l)) ^ n)⁻¹ := by
    rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [h2]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpow) (by positivity)

/-- Comparison of two scales: if `ℓ ≤ L` and `κ L ≤ ℓ` with `κ ≤ 1`, then
`ℓ (1 + |ℓ b|)^{-n} ≤ κ^{-n} L (1 + |L b|)^{-n}`. -/
theorem scale_mul_bracket_le (n : ℕ) {ℓ L κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hℓ : 0 < ℓ)
    (h1 : ℓ ≤ L) (h2 : κ * L ≤ ℓ) (b : ℝ) :
    ℓ * (1 + |ℓ * b|) ^ (-(n : ℝ)) ≤ L * (κ⁻¹) ^ n * (1 + |L * b| ) ^ (-(n : ℝ)) := by
  have hL : 0 < L := hℓ.trans_le h1
  have hℓb : |ℓ * b| = ℓ * |b| := by rw [abs_mul, abs_of_pos hℓ]
  have hLb : |L * b| = L * |b| := by rw [abs_mul, abs_of_pos hL]
  have hy : 0 < 1 + |L * b| := by rw [hLb]; positivity
  have hx : 0 < 1 + |ℓ * b| := by rw [hℓb]; positivity
  have hle : κ * (1 + |L * b|) ≤ 1 + |ℓ * b| := by
    rw [hLb, hℓb]
    have : κ * L * |b| ≤ ℓ * |b| := mul_le_mul_of_nonneg_right h2 (abs_nonneg b)
    nlinarith [abs_nonneg b]
  have hpow : (κ * (1 + |L * b|)) ^ n ≤ (1 + |ℓ * b|) ^ n := pow_le_pow_left₀ (by positivity) hle n
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le, Real.rpow_natCast, Real.rpow_natCast]
  have h3 : ((1 + |ℓ * b|) ^ n)⁻¹ ≤ (κ⁻¹) ^ n * ((1 + |L * b|) ^ n)⁻¹ := by
    calc ((1 + |ℓ * b|) ^ n)⁻¹ ≤ ((κ * (1 + |L * b|)) ^ n)⁻¹ := inv_anti₀ (by positivity) hpow
      _ = _ := by rw [mul_pow, mul_inv, inv_pow]
  calc ℓ * ((1 + |ℓ * b|) ^ n)⁻¹ ≤ L * ((κ⁻¹) ^ n * ((1 + |L * b|) ^ n)⁻¹) :=
        mul_le_mul h1 h3 (by positivity) hL.le
    _ = _ := by ring

/-- A profile bound `|f v| ≤ C (1 + |v|)^{-n}` transfers to the scaled profiles
`r^{-θ} f (r^{-θ} b)`, uniformly for `r ∈ [s, 3s]`. -/
theorem abs_scaled_profile_le {f : ℝ → ℝ} {C : ℝ} (n : ℕ) (hC : 0 ≤ C)
    (hf : ∀ v, |f v| ≤ C * (1 + |v|) ^ (-(n : ℝ))) {θ : ℝ} (hθ : 0 < θ) {s r : ℝ} (hs : 0 < s)
    (hsr : s ≤ r) (hr3 : r ≤ 3 * s) (b : ℝ) :
    |r ^ (-θ) * f (r ^ (-θ) * b)| ≤
      C * (3 ^ θ) ^ n * (s ^ (-θ) * blockBracket n (s ^ θ) b) := by
  have hr : 0 < r := hs.trans_le hsr
  have hℓ : 0 < r ^ (-θ) := Real.rpow_pos_of_pos hr _
  have hL : 0 < s ^ (-θ) := Real.rpow_pos_of_pos hs _
  have hκ : 0 < (3 : ℝ) ^ (-θ) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : r ^ (-θ) ≤ s ^ (-θ) := Real.rpow_le_rpow_of_nonpos hs hsr (by linarith)
  have h2 : (3 : ℝ) ^ (-θ) * s ^ (-θ) ≤ r ^ (-θ) := by
    rw [← Real.mul_rpow (by norm_num) hs.le]
    exact Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
  have hκ1 : (3 : ℝ) ^ (-θ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hκinv : ((3 : ℝ) ^ (-θ))⁻¹ = 3 ^ θ := by
    rw [Real.rpow_neg (by norm_num), inv_inv]
  have key := scale_mul_bracket_le n hκ hκ1 hℓ h1 h2 b
  rw [hκinv] at key
  have hLb : |s ^ (-θ) * b| = |b| / s ^ θ := by
    rw [abs_mul, abs_of_pos hL, Real.rpow_neg hs.le]
    field_simp
  rw [hLb] at key
  have hbr : blockBracket n (s ^ θ) b = (1 + |b| / s ^ θ) ^ (-(n : ℝ)) := rfl
  rw [hbr, abs_mul, abs_of_pos hℓ]
  calc r ^ (-θ) * |f (r ^ (-θ) * b)| ≤ r ^ (-θ) * (C * (1 + |r ^ (-θ) * b|) ^ (-(n : ℝ))) :=
        mul_le_mul_of_nonneg_left (hf _) hℓ.le
    _ = C * (r ^ (-θ) * (1 + |r ^ (-θ) * b|) ^ (-(n : ℝ))) := by ring
    _ ≤ C * (s ^ (-θ) * (3 ^ θ) ^ n * (1 + |b| / s ^ θ) ^ (-(n : ℝ))) :=
        mul_le_mul_of_nonneg_left key hC
    _ = _ := by ring

end RegularityStructures

end
