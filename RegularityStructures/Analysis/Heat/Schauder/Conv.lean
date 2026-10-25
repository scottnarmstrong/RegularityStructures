/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.ShellPairing
public import RegularityStructures.Analysis.Heat.Schauder.ShellPairingBound

/-!
# Convolution of a distribution with the heat kernel

`heatConv Λ x = ∑ₙ ⟨Λ, heatShell n (x - ·)⟩`, the (dyadically decomposed) convolution of `Λ` with the
singular part of the heat kernel [Hai14, Section 5].  For `Λ` of global order `α > -2` the series
is absolutely summable and `|heatConv Λ x| ≤ c₁ C` (`abs_heatConv_le`), the sup-norm case of the
Schauder estimate "`K *` maps `C^α` to `C^{α+2}`".
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `(K * Λ)(x) = ∑ₙ ⟨Λ, K_n(x, ·)⟩`, with `K_n(x, y) = heatShell n (x - y)`. -/
def heatConv (Λ : ℝ → ParabolicSpace → ℝ) (x : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing Λ (fun y => heatShell n (x - y))

/-- The geometric ratio `2^{-(α+2)}` of the shell bounds. -/
def shellRatio (α : ℝ) : ℝ := (2 : ℝ) ^ (-(α + 2))

/-- The constant `c₁(α) = c₀(α) / (1 - 2^{-(α+2)})` of the sup bound. -/
def heatConvConst (α : ℝ) : ℝ := shellPairingConst α / (1 - shellRatio α)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem shellRatio_pos (α : ℝ) : 0 < shellRatio α := Real.rpow_pos_of_pos (by norm_num) _

theorem shellRatio_lt_one {α : ℝ} (hα : -2 < α) : shellRatio α < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem two_rpow_neg_mul_nat (α : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (-(α + 2) * n) = shellRatio α ^ n := by
  rw [shellRatio, ← Real.rpow_mul_natCast (by norm_num)]

theorem heatConvConst_nonneg {α : ℝ} (hα : -2 < α) : 0 ≤ heatConvConst α :=
  div_nonneg (shellPairingConst_nonneg (by linarith)) (sub_nonneg.2 (shellRatio_lt_one hα).le)

/-- **Shell bound** (target 1): `|⟨Λ, K_n(x, ·)⟩| ≤ c₀ C 2^{-(α+2) n}` with `c₀` depending only
on `α`. -/
theorem exists_abs_pairing_heatShell_le {α : ℝ} (hα : -2 < α) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ {Λ : ℝ → ParabolicSpace → ℝ} {C : ℝ},
      Λ ∈ parabolicSemigroup.distributions → (∀ u, 0 < u → Measurable (Λ u)) → 0 ≤ C →
      (∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4)) →
      ∀ (n : ℕ) (x : ParabolicSpace),
        |parabolicSemigroup.pairing Λ (fun y => heatShell n (x - y))| ≤
          c₀ * C * (2 : ℝ) ^ (-(α + 2) * n) :=
  ⟨shellPairingConst α, shellPairingConst_nonneg (by linarith),
    fun hΛ hΛm hC hloc n x => abs_pairing_heatShell_le hΛ hΛm hα hC hloc n x⟩

variable {Λ : ℝ → ParabolicSpace → ℝ} {α C : ℝ}

theorem summable_pairing_heatShell
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hα : -2 < α) (hC : 0 ≤ C)
    (hloc : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4)) (x : ParabolicSpace) :
    Summable fun n : ℕ => parabolicSemigroup.pairing Λ (fun y => heatShell n (x - y)) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (shellRatio_pos α).le (shellRatio_lt_one hα)).mul_left
      (shellPairingConst α * C)) fun n => ?_
  rw [Real.norm_eq_abs, ← two_rpow_neg_mul_nat]
  exact abs_pairing_heatShell_le hΛ hΛm hα hC hloc n x

/-- **Sup bound** (target 2): `|(K * Λ)(x)| ≤ c₁ C` with `c₁ = heatConvConst α`. -/
theorem abs_heatConv_le
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hα : -2 < α) (hC : 0 ≤ C)
    (hloc : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4)) (x : ParabolicSpace) :
    |heatConv Λ x| ≤ heatConvConst α * C := by
  have hg := (hasSum_geometric_of_lt_one (shellRatio_pos α).le (shellRatio_lt_one hα)).mul_left
    (shellPairingConst α * C)
  have h := tsum_of_norm_bounded hg fun n => by
    rw [Real.norm_eq_abs, ← two_rpow_neg_mul_nat]
    exact abs_pairing_heatShell_le hΛ hΛm hα hC hloc n x
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  have : 1 - shellRatio α ≠ 0 := (sub_pos.2 (shellRatio_lt_one hα)).ne'
  rw [heatConvConst]
  field_simp

end RegularityStructures

end
