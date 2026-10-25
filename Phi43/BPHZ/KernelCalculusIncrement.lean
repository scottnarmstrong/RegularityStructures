/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusBasic

/-!
# Interpolated increments of singular kernels

[Hai14, Lemma 10.18] in increment form: if `|f u| ≤ B s(u)^(-a)` and
`|f(u + h) - f u| ≤ B s(h) s(u)^(-a-1)` whenever `s h ≤ s u / 2`, then for every
`θ ∈ [0,1]`
`|f z - f z'| ≤ 12 B s(z - z')^θ (s(z)^(-a-θ) + s(z')^(-a-θ))`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.18, p. 158.
-/

public section

namespace RegularityStructures

private theorem rpow_neg_eq_rpow_mul {x a θ : ℝ} (hx : 0 < x) :
    x ^ (-a) = x ^ θ * x ^ (-a - θ) := by
  rw [← Real.rpow_add hx]; ring_nf

private theorem rpow_le_const_mul_rpow {x d K θ : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hK1 : 1 ≤ K) (h : x ≤ K * d) : x ^ θ ≤ K * d ^ θ := by
  calc
    x ^ θ ≤ (K * d) ^ θ := Real.rpow_le_rpow hx h hθ0
    _ = K ^ θ * d ^ θ := Real.mul_rpow hK hd
    _ ≤ K * d ^ θ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd _)
      calc K ^ θ ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1 hθ1
        _ = K := Real.rpow_one K

/-- [Hai14, Lemma 10.18 (iv)] in increment form. -/
theorem abs_sub_le_of_increment {f : SpaceTime → ℝ} {a B θ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1)
    (hf : ∀ w, 0 < torusParabolicSize w → |f w| ≤ B * torusParabolicSize w ^ (-a))
    (hinc : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |f (u + h) - f u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-a - 1))
    {z z' : SpaceTime} (hz : 0 < torusParabolicSize z) (hz' : 0 < torusParabolicSize z') :
    |f z - f z'| ≤ 12 * B * torusParabolicSize (z - z') ^ θ *
      (torusParabolicSize z ^ (-a - θ) + torusParabolicSize z' ^ (-a - θ)) := by
  set d := torusParabolicSize (z - z') with hd
  have hd0 : 0 ≤ d := torusParabolicSize_nonneg _
  have hdθ : 0 ≤ d ^ θ := Real.rpow_nonneg hd0 _
  have hzθ : 0 ≤ torusParabolicSize z ^ (-a - θ) := Real.rpow_nonneg hz.le _
  have hz'θ : 0 ≤ torusParabolicSize z' ^ (-a - θ) := Real.rpow_nonneg hz'.le _
  have hzz : z = z' + (z - z') := by abel
  rcases le_or_gt d (torusParabolicSize z' / 2) with hcase | hcase
  · have h1 := hinc z' (z - z') hz' hcase
    rw [← hzz] at h1
    have hd1 : d ^ (1 - θ) ≤ torusParabolicSize z' ^ (1 - θ) :=
      Real.rpow_le_rpow hd0 (by linarith) (by linarith)
    have hsplit : d = d ^ θ * d ^ (1 - θ) := by
      by_cases h0 : d = 0
      · by_cases hθ : θ = 0
        · simp [h0, hθ]
        · simp [h0, hθ]
      · rw [← Real.rpow_add (lt_of_le_of_ne hd0 (Ne.symm h0))]; simp
    have hpow : torusParabolicSize z' ^ (1 - θ) * torusParabolicSize z' ^ (-a - 1) =
        torusParabolicSize z' ^ (-a - θ) := by
      rw [← Real.rpow_add hz']; ring_nf
    have hS : 0 ≤ torusParabolicSize z' ^ (-a - 1) := Real.rpow_nonneg hz'.le _
    calc
      |f z - f z'| ≤ B * d * torusParabolicSize z' ^ (-a - 1) := h1
      _ = B * d ^ θ * (d ^ (1 - θ) * torusParabolicSize z' ^ (-a - 1)) := by
        conv_lhs => rw [hsplit]
        ring
      _ ≤ B * d ^ θ * (torusParabolicSize z' ^ (1 - θ) * torusParabolicSize z' ^ (-a - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hdθ)
        exact mul_le_mul_of_nonneg_right hd1 hS
      _ = B * d ^ θ * torusParabolicSize z' ^ (-a - θ) := by rw [hpow]
      _ ≤ _ := by
        have h0 := mul_nonneg hB hdθ
        nlinarith [mul_nonneg h0 hzθ, mul_nonneg h0 hz'θ]
  · have hzd : torusParabolicSize z ≤ 12 * d := by
      have := torusParabolicSize_add_le_four_mul z' (z - z')
      rw [← hzz] at this
      linarith
    have hz'd : torusParabolicSize z' ≤ 12 * d := by linarith
    have e1 := rpow_le_const_mul_rpow hz.le hd0 (by norm_num) hθ0 hθ1 (by norm_num) hzd
    have e2 := rpow_le_const_mul_rpow hz'.le hd0 (by norm_num) hθ0 hθ1 (by norm_num) hz'd
    have b1 : |f z| ≤ B * (12 * d ^ θ * torusParabolicSize z ^ (-a - θ)) := by
      calc
        |f z| ≤ B * torusParabolicSize z ^ (-a) := hf z hz
        _ = B * (torusParabolicSize z ^ θ * torusParabolicSize z ^ (-a - θ)) := by
          rw [← rpow_neg_eq_rpow_mul hz]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hB
          calc torusParabolicSize z ^ θ * torusParabolicSize z ^ (-a - θ)
              ≤ (12 * d ^ θ) * torusParabolicSize z ^ (-a - θ) :=
                mul_le_mul_of_nonneg_right e1 hzθ
            _ = _ := by ring
    have b2 : |f z'| ≤ B * (12 * d ^ θ * torusParabolicSize z' ^ (-a - θ)) := by
      calc
        |f z'| ≤ B * torusParabolicSize z' ^ (-a) := hf z' hz'
        _ = B * (torusParabolicSize z' ^ θ * torusParabolicSize z' ^ (-a - θ)) := by
          rw [← rpow_neg_eq_rpow_mul hz']
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hB
          calc torusParabolicSize z' ^ θ * torusParabolicSize z' ^ (-a - θ)
              ≤ (12 * d ^ θ) * torusParabolicSize z' ^ (-a - θ) :=
                mul_le_mul_of_nonneg_right e2 hz'θ
            _ = _ := by ring
    calc
      |f z - f z'| ≤ |f z| + |f z'| := abs_sub _ _
      _ ≤ _ := by nlinarith

end RegularityStructures

end
