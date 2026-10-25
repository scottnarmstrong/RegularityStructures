/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SupReal
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.WeightedSingularDefs

/-!
# The pieces of one scale in the sup bound for `𝒦_γ f`

For `x` in the time slab, `w = ‖x‖_P`, `u = 2^n` and `t = u w`, with `L = |k|_𝔰` and
`ηK = α ∧ η + 2`, the three pieces entering the term of scale `n` of the `X^k` coefficient obey

* `exists_abs_latticeRecon_shell_le_weight` (layer): `|⟨R f, D^k K_n(x − ·)⟩| ≤ C K₀ C_f w^{ηK − L} t^{L−2−α∧η}`;
* `exists_abs_latticeRecon_shell_le_weight_small` (time-Taylor, `t < 1`):
  the same with `t^{2m + L − 2 − α∧η}`;
* `exists_abs_fx_mul_pairing_shell_le` : `|f(x)_i ⟨Π_x e_i, D^k K_n(x − ·)⟩| ≤ C K₀ C_f w^{ηK − L} t^{L−2−deg i}`
  for `α ≤ deg i < γ`;
* `exists_abs_singShellPairing_le_weight` (local, `t ≥ 64`):
  `|⟨R f − Π_x f(x), D^k K_n(x − ·)⟩| ≤ C K₀ C_f w^{ηK − L} t^{L−2−γ}`.
-/

public section

open Set Filter

namespace RegularityStructures.KGammaSup

/-- `u^e = t^e w^{-e}` for `t = u w`. -/
theorem rpow_eq_rpow_mul_rpow_neg {u w : ℝ} (hu : 0 < u) (hw : 0 < w) (e : ℝ) :
    u ^ e = (u * w) ^ e * w ^ (-e) := by
  rw [Real.mul_rpow hu.le hw.le, mul_assoc, ← Real.rpow_add hw]
  simp

/-- `c u^e w^s ≤ c t^e w^{s'}` if `w ≤ 1` and `s' ≤ s − e`. -/
theorem mul_rpow_mul_rpow_le {u w c e s s' : ℝ} (hu : 0 < u) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 ≤ c) (h : s' ≤ s - e) :
    c * u ^ e * w ^ s ≤ c * (u * w) ^ e * w ^ s' := by
  have h1 : c * u ^ e * w ^ s = c * (u * w) ^ e * w ^ (s - e) := by
    rw [rpow_eq_rpow_mul_rpow_neg hu hw e, mul_assoc c, mul_assoc c, mul_assoc,
      ← Real.rpow_add hw]
    congr 3; ring
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc (Real.rpow_nonneg (by positivity) _))
  exact Real.rpow_le_rpow_of_exponent_ge hw hw1 h

theorem weight_pos {T : ℝ} {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    0 < singularWeight timeZeroDist x :=
  singularWeight_pos (timeZeroDist_pos_of_mem_timeSlab hx)

/-- If `w < 1` then `w² = x₀` (`w = |x₀|^{1/2}`). -/
theorem weight_sq_eq {T : ℝ} {x : ParabolicSpace} (hx : x ∈ timeSlab T)
    (hw : singularWeight timeZeroDist x < 1) : singularWeight timeZeroDist x ^ 2 = x.1 := by
  have h1 : timeZeroDist x < 1 := by
    unfold singularWeight at hw
    rcases min_lt_iff.1 hw with h | h
    · exact absurd h (lt_irrefl _)
    · exact h
  have h2 : singularWeight timeZeroDist x = timeZeroDist x := min_eq_right h1.le
  rw [h2]
  unfold timeZeroDist
  rw [Real.sq_sqrt (abs_nonneg _), abs_of_pos hx.1]

/-- `t = 2^n w < 1` forces `x₀ ≤ 4^{-n}`. -/
theorem le_inv_sq_of_scale_lt_one {T : ℝ} {x : ParabolicSpace} (hx : x ∈ timeSlab T) (n : ℕ)
    (ht : (2 : ℝ) ^ n * singularWeight timeZeroDist x < 1) :
    x.1 ≤ (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hw := weight_pos hx
  have hu1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hw1 : singularWeight timeZeroDist x < 1 := by nlinarith
  rw [← weight_sq_eq hx hw1]
  have : singularWeight timeZeroDist x ≤ ((2 : ℝ) ^ n)⁻¹ := by
    rw [← one_div, le_div_iff₀ hu]; linarith
  exact pow_le_pow_left₀ hw.le this 2

end RegularityStructures.KGammaSup

end
