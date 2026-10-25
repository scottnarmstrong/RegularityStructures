/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real

/-!
# Iterating a local Lipschitz step over restarts

The restart argument behind the continuity of the stopped solutions in the model [Hai14,
Proposition 7.11, Corollary 7.12], in abstract form.  A distance
`D : ℝ → ℝ≥0∞` along a time interval `[0, T]` with `D 0 = 0` that obeys the local step
`D t ≤ K (D s + d)` whenever `0 ≤ s ≤ t ≤ s + t₀ ≤ …`, `t ≤ T`, satisfies `D t ≤ c_n d` on
`[0, n t₀] ∩ [0, T]`, where `c_0 = 0`, `c_{n+1} = K (c_n + 1)` (`iterConst`).  Choosing `n` with
`T ≤ n t₀` gives the global bound used for the stopped continuity of classical solutions
(`stoppedContinuity_of_localLipschitzBody`).
-/

public section

open ENNReal

namespace RegularityStructures.Phi43.StoppedContinuity

/-- The constants of the iteration: `c_0 = 0`, `c_{n+1} = K (c_n + 1)`. -/
noncomputable def iterConst (K : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => K * (iterConst K n + 1)

theorem iterConst_nonneg {K : ℝ} (hK : 0 ≤ K) : ∀ n, 0 ≤ iterConst K n
  | 0 => le_rfl
  | n + 1 => mul_nonneg hK (by linarith [iterConst_nonneg hK n])

theorem iterConst_mono {K : ℝ} (hK : 1 ≤ K) (n : ℕ) : iterConst K n ≤ iterConst K (n + 1) := by
  have h0 := iterConst_nonneg (zero_le_one.trans hK) n
  change iterConst K n ≤ K * (iterConst K n + 1)
  nlinarith

theorem one_le_iterConst {K : ℝ} (hK : 1 ≤ K) : ∀ n, 1 ≤ n → 1 ≤ iterConst K n
  | 0, h => absurd h (by norm_num)
  | n + 1, _ => by
      have h0 := iterConst_nonneg (zero_le_one.trans hK) n
      change 1 ≤ K * (iterConst K n + 1)
      nlinarith

/-- **Iteration of a local Lipschitz step.** -/
theorem le_iterConst_mul {D : ℝ → ℝ≥0∞} (hD0 : D 0 = 0) {t₀ K d T : ℝ} (ht₀ : 0 < t₀)
    (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hstep : ∀ s t, 0 ≤ s → s ≤ t → t ≤ s + t₀ → t ≤ T →
      D t ≤ ENNReal.ofReal K * (D s + ENNReal.ofReal d)) :
    ∀ n : ℕ, ∀ t, 0 ≤ t → t ≤ n * t₀ → t ≤ T → D t ≤ ENNReal.ofReal (iterConst K n * d) := by
  intro n
  induction n with
  | zero =>
    intro t ht0 ht hT
    have : t = 0 := le_antisymm (by simpa using ht) ht0
    subst this
    simp [hD0]
  | succ n ih =>
    intro t ht0 ht hT
    have hc := iterConst_nonneg (zero_le_one.trans hK) n
    by_cases hle : t ≤ n * t₀
    · refine (ih t ht0 hle hT).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (iterConst_mono hK n) hd
    · push Not at hle
      have hs0 : 0 ≤ (n : ℝ) * t₀ := mul_nonneg (Nat.cast_nonneg n) ht₀.le
      have hst : t ≤ n * t₀ + t₀ := by push_cast at ht; linarith
      have h1 := hstep (n * t₀) t hs0 hle.le hst hT
      have h2 := ih (n * t₀) hs0 le_rfl (hle.le.trans hT)
      calc D t ≤ ENNReal.ofReal K * (D (n * t₀) + ENNReal.ofReal d) := h1
        _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (iterConst K n * d) + ENNReal.ofReal d) := by
            gcongr
        _ = ENNReal.ofReal (iterConst K (n + 1) * d) := by
            rw [← ENNReal.ofReal_add (mul_nonneg hc hd) hd,
              ← ENNReal.ofReal_mul (zero_le_one.trans hK)]
            congr 1
            change K * (iterConst K n * d + d) = K * (iterConst K n + 1) * d
            ring

end RegularityStructures.Phi43.StoppedContinuity

end
