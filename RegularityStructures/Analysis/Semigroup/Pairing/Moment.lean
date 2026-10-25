/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Kernel moments against a distribution of local order `γ`

If `Λ` is of order `γ` at `x₀` (`IsLocalOrder`), the kernel moment bounds control
`∫ |Q_v(y, z)| |Λ_s(z)| dz` uniformly in `v ≤ h₀` and in the points `y` with `d(y, x₀) ≤ λ`
(`exists_integral_abs_kernel_mul_le`); this is the integrability input for the Fubini arguments in
`RegularityStructures.Analysis.Semigroup.Pairing.Swap`.

* `LocalData`: bundle of the standing hypotheses on `Λ`;
* `abs_le_of_isLocalOrder`: `|Λ_u(y)| ≤ C ∑ u^{a/ℓ} λ^{γ-a}` where `d(y, x₀) ≤ λ`;
* `rpow_add_le_mul`: `(x + y)^r ≤ 2^r (x^r + y^r)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

theorem rpow_add_le_mul {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hr : 0 ≤ r) :
    (x + y) ^ r ≤ 2 ^ r * (x ^ r + y ^ r) := by
  have h1 : x + y ≤ 2 * max x y := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hm : 0 ≤ max x y := le_max_of_le_left hx
  calc (x + y) ^ r ≤ (2 * max x y) ^ r := Real.rpow_le_rpow (by positivity) h1 hr
    _ = 2 ^ r * (max x y) ^ r := Real.mul_rpow (by norm_num) hm
    _ ≤ 2 ^ r * (x ^ r + y ^ r) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
      have hx' := Real.rpow_nonneg hx r
      have hy' := Real.rpow_nonneg hy r
      rcases le_total x y with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith

end RegularityStructures.RegularisingSemigroup

end
