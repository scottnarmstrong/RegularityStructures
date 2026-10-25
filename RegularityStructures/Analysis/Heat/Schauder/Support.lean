/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Basic
public import RegularityStructures.Analysis.Parabolic.TestFunctionExists

/-!
# A sharper support radius for the heat shells

`parabolicNorm z ≤ 3 · smoothParabolicNorm z`, hence `heatShell n` vanishes outside
`‖z‖_𝔰 ≤ (3/4) 2^{-n}`.  The slack (compared with `heatShell_eq_zero`, radius `2^{-n}`) lets the
increment `heatShell n w - heatShell n (w - e)` stay inside the unit ball when `n = 0`, which the
pairing bound (scales `lam ≤ 1`) requires.
-/

public section

namespace RegularityStructures

theorem parabolicNorm_le_three_mul_smoothParabolicNorm (z : ParabolicSpace) :
    parabolicNorm z ≤ 3 * smoothParabolicNorm z := by
  have hN := smoothParabolicNorm_nonneg z
  have h4 := smoothParabolicNorm_pow_four z
  have hs := sqNorm3_nonneg z.2
  have hsN : sqNorm3 z.2 ≤ smoothParabolicNorm z ^ 2 := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg z.1, sq_nonneg (smoothParabolicNorm z),
      mul_pos (lt_of_le_of_lt (sq_nonneg _) h) (lt_of_le_of_lt (sq_nonneg _) h)]
  have ht : Real.sqrt |z.1| ≤ smoothParabolicNorm z := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hN ?_
    rw [h4]
    have : Real.sqrt |z.1| ^ 4 = z.1 ^ 2 := by
      have := Real.sq_sqrt (abs_nonneg z.1)
      calc Real.sqrt |z.1| ^ 4 = (Real.sqrt |z.1| ^ 2) ^ 2 := by ring
        _ = z.1 ^ 2 := by rw [this, sq_abs]
    rw [this]
    nlinarith [sq_nonneg (sqNorm3 z.2)]
  have hsum : ∑ i, |z.2 i| ≤ 2 * smoothParabolicNorm z := by
    have hsq : (∑ i, |z.2 i|) ^ 2 ≤ (2 * smoothParabolicNorm z) ^ 2 := by
      simp only [Fin.sum_univ_three]
      have e : sqNorm3 z.2 = z.2 0 ^ 2 + z.2 1 ^ 2 + z.2 2 ^ 2 := by
        simp [sqNorm3, Fin.sum_univ_three]
      rw [e] at hsN
      nlinarith [sq_abs (z.2 0), sq_abs (z.2 1), sq_abs (z.2 2),
        sq_nonneg (|z.2 0| - |z.2 1|), sq_nonneg (|z.2 0| - |z.2 2|),
        sq_nonneg (|z.2 1| - |z.2 2|)]
    exact le_of_sq_le_sq (by simpa using hsq) (by linarith)
  unfold parabolicNorm
  linarith

theorem heatShell_eq_zero_of_gt {n : ℕ} {z : ParabolicSpace}
    (h : 3 / 4 * (2 : ℝ)⁻¹ ^ n < parabolicNorm z) : heatShell n z = 0 := by
  have h3 := parabolicNorm_le_three_mul_smoothParabolicNorm z
  have hpos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have e : 3 / 4 * (2 : ℝ)⁻¹ ^ n = 3 * (1 / 4 / 2 ^ n) := by
    rw [inv_pow]; field_simp
  have h2 : 2 ≤ (2 : ℝ) ^ (n + 3) * smoothParabolicNorm z := by
    have hN : 1 / 4 / (2 : ℝ) ^ n < smoothParabolicNorm z := by linarith
    rw [div_lt_iff₀ hpos] at hN
    rw [pow_add]
    nlinarith
  simp [heatShell, dyadicBump_eq_zero_of_ge h2]

end RegularityStructures

end
