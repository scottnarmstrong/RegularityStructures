/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorPairing
public import RegularityStructures.Analysis.Heat.Schauder.TaylorPairingCentre
public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.DerivativePairing

/-!
# Small scales: pairing of the shell centred at `y` against `Λ` of local order at `x`

For `h` smooth, vanishing outside the unit parabolic ball, and `Λ` of local order `γ` at `x`
(exponents `A`), the `n`-th shell centred at `y` satisfies

  `|⟨Λ, scaledShell h n (y - ·)⟩| ≤ c C ∑_{a ∈ A} κ_a 2^{-(a+2) n} (2^{-n} + d(y, x))^{γ - a}`
  (`abs_pairing_scaledShell_centre_le`),

`c = ∫ |h| + ∫ |L h|` (`κ_a = pairingWeight a`).  In the regime `2^{-n} ≤ d(y, x)` this is
`≲ C ∑_a 2^{-(a+2) n} d(y, x)^{γ - a}`.
Together with the derivative-shell bound `abs_pairing_lineIter_scaledShell_le` (centre `x`) this
gives the two separate bounds of [Hai14, proof of Lemma 5.19] for `2^{-n} < d(x, y)`.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem tendsto_and_abs_pairing_scaledShell_centre_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x y : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C) (n : ℕ) :
    Filter.Tendsto (fun s => ∫ z, Λ s z * scaledShell h n (y - z)) (nhdsWithin 0 (Ioi 0))
        (nhds (parabolicSemigroup.pairing Λ (fun z => scaledShell h n (y - z)))) ∧
    |parabolicSemigroup.pairing Λ (fun z => scaledShell h n (y - z))| ≤
      ((∫ w, |h w|) + ∫ w, |parabolicGenerator h w|) * C *
        ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
          ((2 : ℝ)⁻¹ ^ n + parabolicNorm (y - x)) ^ (γ - a)) := by
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlam : (0 : ℝ) < 2⁻¹ ^ n := by positivity
  have hlam2 : (2 : ℝ)⁻¹ ^ n ≤ 2 :=
    (pow_le_one₀ (by norm_num) (by norm_num)).trans (by norm_num)
  have hrp : ((2 : ℝ)⁻¹ ^ n) ^ (-(4 : ℝ)) = ((2 : ℝ) ^ n) ^ 4 := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
    simp [inv_pow]
  have key := tendsto_and_abs_pairing_reflect_le_centre hΛ hΛm hA hC hloc (contDiff_scaledShell h0 n) hlam
    hlam2 (fun w hw => scaledShell_eq_zero hs hw)
    (B₀ := ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |h w|)
    (B₁ := ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |parabolicGenerator h w|)
    (integral_abs_scaledShell h n).le
    (by
      rw [integral_abs_parabolicGenerator_scaledShell h0, hrp]
      exact le_of_eq (by field_simp))
    (c := y)
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  have hsum : ∑ a ∈ A, pairingWeight a * (((2 : ℝ)⁻¹ ^ n) ^ a *
      ((2 : ℝ)⁻¹ ^ n + parabolicNorm (y - x)) ^ (γ - a)) =
      ((2 : ℝ) ^ n) ^ 2 * ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
        ((2 : ℝ)⁻¹ ^ n + parabolicNorm (y - x)) ^ (γ - a)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : ((2 : ℝ)⁻¹ ^ n) ^ a = ((2 : ℝ) ^ n) ^ 2 * (2 : ℝ) ^ (-(a + 2) * n) := by
      rw [two_inv_pow_rpow, ← two_rpow_natCast_mul 2 n, ← Real.rpow_add (by norm_num)]
      congr 1; push_cast; ring
    rw [e]; ring
  rw [hsum]
  have hN2 : ((2 : ℝ) ^ n) ^ 2 * ((2 : ℝ) ^ n)⁻¹ ^ 2 = 1 := by field_simp
  linear_combination (C * (∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
      ((2 : ℝ)⁻¹ ^ n + parabolicNorm (y - x)) ^ (γ - a))) *
      ((∫ w, |h w|) + ∫ w, |parabolicGenerator h w|)) * hN2

theorem abs_pairing_scaledShell_centre_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x y : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C) (n : ℕ) :
    |parabolicSemigroup.pairing Λ (fun z => scaledShell h n (y - z))| ≤
      ((∫ w, |h w|) + ∫ w, |parabolicGenerator h w|) * C *
        ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
          ((2 : ℝ)⁻¹ ^ n + parabolicNorm (y - x)) ^ (γ - a)) :=
  (tendsto_and_abs_pairing_scaledShell_centre_le hΛ hΛm h0 hs hA hC hloc n).2

end RegularityStructures

end
