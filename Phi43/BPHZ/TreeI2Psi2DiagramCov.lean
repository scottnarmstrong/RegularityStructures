/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramInner

/-!
# The kernel increment and the covariance weights

`i2Psi2Increment K x y w = K(y - w) - K(x - w)` is the kernel `δK_x(y, w)` of [Hai14, (10.39)].
A covariance `Q` with `|Q u| ≤ B s(u)^(-1)` satisfies the flipped bound
`|Q(w - g)| ≤ 2 B s(g - w)^(-1)` (`abs_cov_flip_le`), and its square
`Q(w - g)² ≤ 4 B² s(g - w)^(-2)` (`sq_cov_flip_le`), so that it can be paired with the weights
of `TreeI2Psi2DiagramInner`, which are written with `s(g - w)`.
-/

@[expose] public section

namespace RegularityStructures

/-- The kernel increment `δK_x(y, w) = K(y - w) - K(x - w)` of [Hai14, (10.39)]. -/
def i2Psi2Increment (K : SpaceTime → ℝ) (x y w : SpaceTime) : ℝ :=
  K (y - w) - K (x - w)

end RegularityStructures

end

public section

namespace RegularityStructures

theorem torusParabolicSize_pos_of_sub_pos {a b : SpaceTime} (h : 0 < torusParabolicSize (a - b)) :
    0 < torusParabolicSize (b - a) := by
  have h2 := torusParabolicSize_neg_le_two_mul (b - a)
  rw [neg_sub] at h2
  linarith

/-- `s(u)^(-e) ≤ 2^e s(-u)^(-e)`. -/
theorem torusParabolicSize_rpow_neg_le_flip {e : ℝ} (he : 0 ≤ e) {u : SpaceTime}
    (hu : 0 < torusParabolicSize (-u)) :
    torusParabolicSize u ^ (-e) ≤ 2 ^ e * torusParabolicSize (-u) ^ (-e) := by
  have h2 := torusParabolicSize_neg_le_two_mul u
  have hh : torusParabolicSize (-u) * 2⁻¹ ≤ torusParabolicSize u := by linarith
  have h1 : torusParabolicSize u ^ (-e) ≤ (torusParabolicSize (-u) * 2⁻¹) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hh (neg_nonpos.2 he)
  have h3 : (2⁻¹ : ℝ) ^ (-e) = 2 ^ e := by
    rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  rw [Real.mul_rpow hu.le (by norm_num), h3, mul_comm] at h1
  exact h1

/-- The flipped covariance bound `|Q(w - g)| ≤ 2 B s(g - w)^(-1)`. -/
theorem abs_cov_flip_le {Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {g w : SpaceTime}
    (h : 0 < torusParabolicSize (g - w)) :
    |Q (w - g)| ≤ 2 * B * torusParabolicSize (g - w) ^ (-(1 : ℝ)) := by
  have hpos : 0 < torusParabolicSize (w - g) := torusParabolicSize_pos_of_sub_pos h
  have h1 := hQ (w - g) hpos
  have hn : -(w - g) = g - w := neg_sub w g
  have h2 := torusParabolicSize_rpow_neg_le_flip (e := 1) zero_le_one (u := w - g)
    (by rw [hn]; exact h)
  rw [hn, Real.rpow_one] at h2
  calc |Q (w - g)| ≤ B * torusParabolicSize (w - g) ^ (-(1 : ℝ)) := h1
    _ ≤ B * (2 * torusParabolicSize (g - w) ^ (-(1 : ℝ))) := mul_le_mul_of_nonneg_left h2 hB
    _ = _ := by ring

/-- The flipped square bound `Q(w - g)² ≤ 4 B² s(g - w)^(-2)`. -/
theorem sq_cov_flip_le {Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {g w : SpaceTime}
    (h : 0 < torusParabolicSize (g - w)) :
    Q (w - g) ^ 2 ≤ 4 * B ^ 2 * torusParabolicSize (g - w) ^ (-(2 : ℝ)) := by
  have h1 := abs_cov_flip_le hB hQ h
  have h2 : |Q (w - g)| ^ 2 ≤ (2 * B * torusParabolicSize (g - w) ^ (-(1 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (torusParabolicSize (g - w) ^ (-(1 : ℝ))) ^ 2 = torusParabolicSize (g - w) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]
    norm_num
  rw [sq_abs] at h2
  calc Q (w - g) ^ 2 ≤ (2 * B * torusParabolicSize (g - w) ^ (-(1 : ℝ))) ^ 2 := h2
    _ = 4 * B ^ 2 * (torusParabolicSize (g - w) ^ (-(1 : ℝ))) ^ 2 := by ring
    _ = _ := by rw [h3]

theorem measurable_i2Psi2Increment {K : SpaceTime → ℝ} (hK : Measurable K) (x y : SpaceTime) :
    Measurable (i2Psi2Increment K x y) :=
  (hK.comp (measurable_const.sub measurable_id)).sub (hK.comp (measurable_const.sub measurable_id))

/-- The square bound `Q(u)² ≤ B² s(u)^(-2)`. -/
theorem sq_cov_le {Q : SpaceTime → ℝ} {B : ℝ}
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {u : SpaceTime}
    (h : 0 < torusParabolicSize u) :
    Q u ^ 2 ≤ B ^ 2 * torusParabolicSize u ^ (-(2 : ℝ)) := by
  have h1 := hQ u h
  have h2 : |Q u| ^ 2 ≤ (B * torusParabolicSize u ^ (-(1 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (torusParabolicSize u ^ (-(1 : ℝ))) ^ 2 = torusParabolicSize u ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]
    norm_num
  rw [sq_abs] at h2
  calc Q u ^ 2 ≤ (B * torusParabolicSize u ^ (-(1 : ℝ))) ^ 2 := h2
    _ = B ^ 2 * (torusParabolicSize u ^ (-(1 : ℝ))) ^ 2 := by ring
    _ = _ := by rw [h3]

/-- `s(a - b)^(-e) ≤ 2 s(b - a)^(-e)` for `0 ≤ e ≤ 1`. -/
theorem torusParabolicSize_sub_rpow_neg_le {a b : SpaceTime} {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (h : 0 < torusParabolicSize (b - a)) :
    torusParabolicSize (a - b) ^ (-e) ≤ 2 * torusParabolicSize (b - a) ^ (-e) := by
  have h1 := torusParabolicSize_rpow_neg_le_flip he0 (u := a - b) (by rw [neg_sub]; exact h)
  rw [neg_sub] at h1
  have h2 : (2 : ℝ) ^ e ≤ 2 := by
    calc (2 : ℝ) ^ e ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
      _ = 2 := Real.rpow_one 2
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg h.le _))

end RegularityStructures

end
