/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesAux
public import RegularityStructures.Abstract.Singular.KGamma.SeriesLinear

/-!
# The series for the polynomial components of `Γ_{yx} I e_i`: small scales, window version

For `s = 2^n d > 1` the term `extU n` is estimated directly from its definition by termwise
bounds (`exists_abs_extU_le_of_one_lt_win_near`):
`|extU n| ≤ C CΠ max(C_Γ, 1)² d^σ s^{-b}`, `σ = deg i + 2 − |k|_𝔰`, with `b > 0` and `C`
independent of the model.  The scale-comparison lemmas `scale_term_le_of_one_le`,
`scale_term_le_of_le_one` are also used for the large scales.

Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.21, case `‖x − y‖ ≥ 2^{-n}`, (5.40).
-/

public section

open Set

namespace RegularityStructures

/-- Scale comparison for `s = u d ≥ 1`: `W d^a u^p ≤ W d^σ s^{-b}` if `a − p = σ`, `p = −b'`,
`b ≤ b'`. -/
theorem scale_term_le_of_one_le {d u : ℝ} (hd : 0 < d) (hu : 0 < u) (hs1 : 1 ≤ u * d)
    {a p σ b b' : ℝ} (hσ : a - p = σ) (hp : p = -b') (hb : b ≤ b') (W : ℝ) (hW : 0 ≤ W) :
    W * (d ^ a * u ^ p) ≤ W * (d ^ σ * (u * d) ^ (-b)) := by
  refine mul_le_mul_of_nonneg_left ?_ hW
  rw [rpow_mul_rpow_scale hd hu a p, hσ, hp]
  exact mul_le_mul_of_nonneg_left (rpow_neg_le_of_one_le hs1 hb) (Real.rpow_nonneg hd.le _)

/-- Scale comparison for `s = u d ≤ 1`: `W d^a u^p ≤ W d^σ s^{c}` if `a − p = σ`, `p = c'`,
`c ≤ c'`. -/
theorem scale_term_le_of_le_one {d u : ℝ} (hd : 0 < d) (hu : 0 < u) (hs1 : u * d ≤ 1)
    {a p σ c c' : ℝ} (hσ : a - p = σ) (hp : p = c') (hc : c ≤ c') (W : ℝ) (hW : 0 ≤ W) :
    W * (d ^ a * u ^ p) ≤ W * (d ^ σ * (u * d) ^ c) := by
  refine mul_le_mul_of_nonneg_left ?_ hW
  rw [rpow_mul_rpow_scale hd hu a p, hσ, hp]
  exact mul_le_mul_of_nonneg_left (rpow_le_of_le_one (mul_pos hu hd) hs1 hc)
    (Real.rpow_nonneg hd.le _)

end RegularityStructures

end
