/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import RegularityStructures.Analysis.Heat.Schauder.ShellPairing
public import RegularityStructures.Analysis.Heat.Schauder.ShellPairingBound
public import RegularityStructures.Analysis.Heat.Annihilating.ScaledDeriv
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeReflect

/-!
# Pairings with derivatives of the scaled shells

Bounds and summability of `⟨Λ, D^k K_n⟩` for the scaled shells
(`abs_pairing_lineIter_scaledShell_le`, `summable_pairing_lineIter_scaledShell`,
`abs_tsum_pairing_lineIter_scaledShell_le`).

Source: [Hai14, proof of Theorem 5.12].
-/

@[expose] public noncomputable section

namespace RegularityStructures

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem derivShellConst_nonneg (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ) {A : Finset ℝ} {α : ℝ}
    (hA : ∀ a ∈ A, -4 < a ∧ a ≤ α) : 0 ≤ derivShellConst h k A := by
  refine mul_nonneg ?_ (add_nonneg (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _))
  refine Finset.sum_nonneg fun a ha => ?_
  have : 0 < a + 4 := by linarith [(hA a ha).1]
  have h4 : (0 : ℝ) ≤ 4 / (a + 4) := by positivity
  have : parabolicSemigroup.order = 4 := rfl
  rw [this]
  linarith

theorem abs_pairing_lineIter_scaledShell_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    (k : Fin 4 →₀ ℕ) {x : ParabolicSpace} {α C : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -4 < a ∧ a ≤ α) (hC : 0 ≤ C) (hloc : parabolicSemigroup.IsLocalOrder Λ x α A C)
    (n : ℕ) :
    |derivShellPairing Λ h k x n| ≤
      derivShellConst h k A * C * (2 : ℝ) ^ (((multiDeg k : ℝ) - α - 2) * n) := by
  set G := lineIter (multiDirs k) h with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_lineIter h0 _
  have hGz : ∀ z, 1 < parabolicNorm z → G z = 0 := fun z hz => lineIter_eq_zero_of_lt hs _ hz
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlam : (0 : ℝ) < 2⁻¹ ^ n := by positivity
  have hlam1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set m := multiDeg k with hm
  set T : ParabolicSpace → ℝ := fun w => ((2 : ℝ) ^ n) ^ m * scaledShell G n w with hT
  have hfun : derivShellPairing Λ h k x n = parabolicSemigroup.pairing Λ (fun y => T (x - y)) := by
    rw [derivShellPairing, lineIter_multiDirs_scaledShell h0]
  have hTs : ContDiff ℝ ∞ T := contDiff_const.mul (contDiff_scaledShell hGs n)
  have hTz : ∀ w, 2⁻¹ ^ n < parabolicNorm w → T w = 0 := fun w hw => by
    simp [hT, scaledShell_eq_zero hGz hw]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ n) ^ m := by positivity
  have hI0 : ∫ w, |T w| = ((2 : ℝ) ^ n) ^ m * (((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |G w|) := by
    have : ∀ w, |T w| = ((2 : ℝ) ^ n) ^ m * |scaledShell G n w| := fun w => by
      rw [hT, abs_mul, abs_of_pos hpos]
    simp_rw [this]
    rw [integral_const_mul, integral_abs_scaledShell]
  have hI1 : ∫ w, |parabolicGenerator T w| =
      ((2 : ℝ) ^ n) ^ m * (((2 : ℝ) ^ n) ^ 2 * ∫ w, |parabolicGenerator G w|) := by
    have hL : parabolicGenerator T = fun w => ((2 : ℝ) ^ n) ^ m *
        parabolicGenerator (scaledShell G n) w :=
      parabolicGenerator_const_mul (contDiff_scaledShell hGs n) _
    have : ∀ w, |parabolicGenerator T w| = ((2 : ℝ) ^ n) ^ m *
        |parabolicGenerator (scaledShell G n) w| := fun w => by
      rw [hL, abs_mul, abs_of_pos hpos]
    simp_rw [this]
    rw [integral_const_mul, integral_abs_parabolicGenerator_scaledShell hGs]
  have hrp : ((2 : ℝ)⁻¹ ^ n) ^ (-(4 : ℝ)) = ((2 : ℝ) ^ n) ^ 4 := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
    simp [inv_pow]
  have key := abs_pairing_reflect_le_of_localOrder hΛ hΛm hA hC hloc hTs hlam hlam1 hTz
    (B₀ := ((2 : ℝ) ^ n) ^ m * (((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |G w|))
    (B₁ := ((2 : ℝ) ^ n) ^ m * (((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |parabolicGenerator G w|))
    hI0.le (by rw [hI1, hrp]; exact le_of_eq (by field_simp))
  rw [hfun]
  refine key.trans (le_of_eq ?_)
  have hqα : ((2 : ℝ)⁻¹ ^ n) ^ α = (2 : ℝ) ^ (-α * n) := two_inv_pow_rpow n α
  have hexp : (2 : ℝ) ^ (((m : ℝ) - α - 2) * n) =
      ((2 : ℝ) ^ n) ^ m * (((2 : ℝ) ^ n)⁻¹ ^ 2) * (2 : ℝ) ^ (-α * n) := by
    have : ((m : ℝ) - α - 2) * n = (m : ℝ) * n + (-2 * n) + (-α * n) := by ring
    rw [this, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), two_rpow_natCast_mul,
      two_rpow_neg_two_mul]
  rw [hqα, hexp, derivShellConst]
  ring

theorem summable_pairing_lineIter_scaledShell {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    (k : Fin 4 →₀ ℕ) {x : ParabolicSpace} {α C : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -4 < a ∧ a ≤ α) (hC : 0 ≤ C) (hloc : parabolicSemigroup.IsLocalOrder Λ x α A C)
    (hk : (multiDeg k : ℝ) < α + 2) : Summable (derivShellPairing Λ h k x) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (derivShellRatio_nonneg k α) (derivShellRatio_lt_one hk)).mul_left
      (derivShellConst h k A * C)) fun n => ?_
  rw [Real.norm_eq_abs, ← two_rpow_deriv_mul_nat]
  exact abs_pairing_lineIter_scaledShell_le hΛ hΛm h0 hs k hA hC hloc n

theorem abs_tsum_pairing_lineIter_scaledShell_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    (k : Fin 4 →₀ ℕ) {x : ParabolicSpace} {α C : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -4 < a ∧ a ≤ α) (hC : 0 ≤ C) (hloc : parabolicSemigroup.IsLocalOrder Λ x α A C)
    (hk : (multiDeg k : ℝ) < α + 2) :
    |∑' n, derivShellPairing Λ h k x n| ≤
      derivShellConst h k A / (1 - derivShellRatio k α) * C := by
  have hg : HasSum (fun n : ℕ => derivShellConst h k A * C * derivShellRatio k α ^ n)
      (derivShellConst h k A * C * (1 - derivShellRatio k α)⁻¹) :=
    (hasSum_geometric_of_lt_one (derivShellRatio_nonneg k α)
      (derivShellRatio_lt_one hk)).mul_left (derivShellConst h k A * C)
  have hb := tsum_of_norm_bounded hg fun n => by
    rw [Real.norm_eq_abs, ← two_rpow_deriv_mul_nat]
    exact abs_pairing_lineIter_scaledShell_le hΛ hΛm h0 hs k hA hC hloc n
  rw [Real.norm_eq_abs] at hb
  refine hb.trans (le_of_eq ?_)
  have : 1 - derivShellRatio k α ≠ 0 := (sub_pos.2 (derivShellRatio_lt_one hk)).ne'
  field_simp

end RegularityStructures

end
