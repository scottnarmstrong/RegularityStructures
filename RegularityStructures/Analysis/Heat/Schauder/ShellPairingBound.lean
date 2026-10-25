/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.ShellPairing
public import RegularityStructures.Analysis.Heat.Schauder.Shell
public import RegularityStructures.Analysis.Heat.Schauder.ShellIntegral

/-!
# Pairing bound for a heat shell

`abs_pairing_heatShell_le`: `|⟨Λ, heatShell n (x - ·)⟩| ≤ shellPairingConst α · C · 2^{-(α+2) n}`
for a `Q`-distribution with `|Λ_u| ≤ C u^{α/4}`, `0 < u ≤ 1`, and `α > -2`.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

/-- The constant `c₀(α)` of the shell pairing bound. -/
noncomputable def shellPairingConst (α : ℝ) : ℝ :=
  (1 + 4 / (α + 4)) * ((∫ w, |heatShell 0 w|) + ∫ w, |parabolicGenerator (heatShell 0) w|)

theorem shellPairingConst_nonneg {α : ℝ} (hα : -4 < α) : 0 ≤ shellPairingConst α := by
  unfold shellPairingConst
  have : 0 < α + 4 := by linarith
  positivity

theorem tendsto_and_abs_pairing_heatShell_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {α C : ℝ} (hα : -2 < α) (hC : 0 ≤ C)
    (hloc : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4)) (n : ℕ) (x : ParabolicSpace) :
    Filter.Tendsto (fun s => ∫ y, Λ s y * heatShell n (x - y)) (nhdsWithin 0 (Ioi 0))
        (nhds (parabolicSemigroup.pairing Λ (fun y => heatShell n (x - y)))) ∧
      |parabolicSemigroup.pairing Λ (fun y => heatShell n (x - y))| ≤
        shellPairingConst α * C * (2 : ℝ) ^ (-(α + 2) * n) := by
  have hlam : (0 : ℝ) < 2⁻¹ ^ n := by positivity
  have hlam1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hrp : ((2 : ℝ)⁻¹ ^ n) ^ (-(4 : ℝ)) = ((2 : ℝ) ^ n) ^ 4 := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
    simp [inv_pow]
  have key0 := tendsto_and_abs_pairing_reflect_le hΛ hΛm (by linarith : -4 < α) hC hloc (contDiff_heatShell n)
    (B₀ := ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |heatShell 0 w|)
    (B₁ := ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |parabolicGenerator (heatShell 0) w|) hlam hlam1
    (fun w hw => heatShell_eq_zero hw) (integral_abs_heatShell n).le
    (by
      rw [integral_abs_parabolicGenerator_heatShell, hrp]
      refine le_of_eq ?_
      field_simp) x
  refine ⟨key0.1, key0.2.trans (le_of_eq ?_)⟩
  rw [two_inv_pow_rpow, shellPairingConst]
  have e : (2 : ℝ) ^ (-(α + 2) * n) = ((2 : ℝ) ^ n)⁻¹ ^ 2 * (2 : ℝ) ^ (-α * n) := by
    have : ((2 : ℝ) ^ n)⁻¹ ^ 2 = (2 : ℝ) ^ (-(2 : ℝ) * n) := by
      have := two_inv_pow_rpow n 2
      rw [Real.rpow_two] at this
      rw [← this]; simp [inv_pow]
    rw [this, ← Real.rpow_add (by norm_num)]
    congr 1; ring
  rw [e]
  ring

theorem abs_pairing_heatShell_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {α C : ℝ} (hα : -2 < α) (hC : 0 ≤ C)
    (hloc : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4)) (n : ℕ) (x : ParabolicSpace) :
    |parabolicSemigroup.pairing Λ (fun y => heatShell n (x - y))| ≤
      shellPairingConst α * C * (2 : ℝ) ^ (-(α + 2) * n) :=
  (tendsto_and_abs_pairing_heatShell_le hΛ hΛm hα hC hloc n x).2

end RegularityStructures

end
