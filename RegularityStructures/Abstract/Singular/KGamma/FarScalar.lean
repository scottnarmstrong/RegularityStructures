/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar estimate for far pairs

If `0 < d ≤ W ≤ 64 d` and `W ≤ w ≤ 2 W`, then
`w^{e − s} d^{s − q} ≤ 2^{|e − s|} 64^{c − s} d^{c − q} W^{e − c}` whenever `s ≤ c`.
This is the elementary comparison used for the polynomial components of far pairs in the singular
Schauder estimate [Hai14, Prop. 6.16].
-/

public section

namespace RegularityStructures

/-- `w^p ≤ 2^{|p|} W^p` for `W ≤ w ≤ 2 W`. -/
theorem rpow_le_two_rpow_abs_mul {W w : ℝ} (hW : 0 < W) (h1 : W ≤ w) (h2 : w ≤ 2 * W) (p : ℝ) :
    w ^ p ≤ 2 ^ |p| * W ^ p := by
  have hw : 0 < w := hW.trans_le h1
  have h2p : (1 : ℝ) ≤ 2 ^ |p| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  have hWp : 0 ≤ W ^ p := Real.rpow_nonneg hW.le _
  rcases le_total 0 p with hp | hp
  · calc w ^ p ≤ (2 * W) ^ p := Real.rpow_le_rpow hw.le h2 hp
      _ = 2 ^ p * W ^ p := Real.mul_rpow (by norm_num) hW.le
      _ = 2 ^ |p| * W ^ p := by rw [abs_of_nonneg hp]
  · calc w ^ p ≤ W ^ p := Real.rpow_le_rpow_of_nonpos hW h1 hp
      _ = 1 * W ^ p := (one_mul _).symm
      _ ≤ 2 ^ |p| * W ^ p := mul_le_mul_of_nonneg_right h2p hWp

/-- The far-pair comparison: for `0 < d ≤ W ≤ 64 d`, `W ≤ w ≤ 2 W` and `s ≤ c`,
`w^{e − s} d^{s − q} ≤ 2^{|e − s|} 64^{c − s} (d^{c − q} W^{e − c})`. -/
theorem rpow_mul_rpow_le_far {d W w : ℝ} (hd : 0 < d) (hdW : d ≤ W) (hW64 : W ≤ 64 * d)
    (h1 : W ≤ w) (h2 : w ≤ 2 * W) (e s q c : ℝ) (hs : s ≤ c) :
    w ^ (e - s) * d ^ (s - q) ≤ (2 : ℝ) ^ |e - s| * (64 : ℝ) ^ (c - s) * (d ^ (c - q) * W ^ (e - c)) := by
  have hW : 0 < W := hd.trans_le hdW
  have hw1 := rpow_le_two_rpow_abs_mul hW h1 h2 (e - s)
  have hdp : 0 ≤ d ^ (s - q) := Real.rpow_nonneg hd.le _
  have hratio : (W / d) ^ (c - s) ≤ (64 : ℝ) ^ (c - s) :=
    Real.rpow_le_rpow (div_nonneg hW.le hd.le) ((div_le_iff₀ hd).2 (by linarith)) (by linarith)
  have e1 : W ^ (e - s) = W ^ (c - s) * W ^ (e - c) := by
    rw [← Real.rpow_add hW]; congr 1; ring
  have e2 : d ^ (c - q) = d ^ (c - s) * d ^ (s - q) := by
    rw [← Real.rpow_add hd]; congr 1; ring
  have hdc : 0 < d ^ (c - s) := Real.rpow_pos_of_pos hd _
  have hid : W ^ (e - s) * d ^ (s - q) = (W / d) ^ (c - s) * (d ^ (c - q) * W ^ (e - c)) := by
    rw [Real.div_rpow hW.le hd.le, e1, e2]
    field_simp
  have hpos : 0 ≤ (2 : ℝ) ^ |e - s| * (64 : ℝ) ^ (c - s) := by positivity
  calc w ^ (e - s) * d ^ (s - q) ≤ ((2 : ℝ) ^ |e - s| * W ^ (e - s)) * d ^ (s - q) :=
        mul_le_mul_of_nonneg_right hw1 hdp
    _ = (2 : ℝ) ^ |e - s| * (W ^ (e - s) * d ^ (s - q)) := by ring
    _ = (2 : ℝ) ^ |e - s| * ((W / d) ^ (c - s) * (d ^ (c - q) * W ^ (e - c))) := by rw [hid]
    _ ≤ (2 : ℝ) ^ |e - s| * (64 ^ (c - s) * (d ^ (c - q) * W ^ (e - c))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hratio ?_) (by positivity)
        exact mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hW.le _)
    _ = _ := by ring

end RegularityStructures

end
