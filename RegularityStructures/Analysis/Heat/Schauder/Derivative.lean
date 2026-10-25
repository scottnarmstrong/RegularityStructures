/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import RegularityStructures.Analysis.Heat.Schauder.ShellPairing

/-!
# Pairing with derivatives of the dyadic pieces

For `h` smooth and supported in the unit parabolic ball, a multi-index `k`, and `Λ` of local order
`α` at `x` with exponent set `A`:
`|⟨Λ, D^k (scaledShell h n)(x - ·)⟩| ≤ c C 2^{(|k|_𝔰 - α - 2) n}` (`abs_pairing_lineIter_scaledShell_le`),
with `c = derivShellConst h k A` independent of `Λ, C, x, n`.  If `|k|_𝔰 < α + 2` the series over `n`
converges absolutely (`summable_pairing_lineIter_scaledShell`) and its sum is bounded by
`c C / (1 - 2^{|k|_𝔰 - α - 2})` (`abs_tsum_pairing_lineIter_scaledShell_le`).  This is the estimate
behind Hairer's map `J(x)` [Hai14, (5.11)].
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The constant of the derivative-shell pairing bound. -/
def derivShellConst (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ) (A : Finset ℝ) : ℝ :=
  parabolicSemigroup.pairingConst A *
    ((∫ w, |lineIter (multiDirs k) h w|) +
      ∫ w, |parabolicGenerator (lineIter (multiDirs k) h) w|)

/-- The `n`-th term: `⟨Λ, D^k (scaledShell h n)(x - ·)⟩`. -/
def derivShellPairing (Λ : ℝ → ParabolicSpace → ℝ) (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ)
    (x : ParabolicSpace) (n : ℕ) : ℝ :=
  parabolicSemigroup.pairing Λ (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))

/-- The geometric ratio `2^{|k|_𝔰 - α - 2}`. -/
def derivShellRatio (k : Fin 4 →₀ ℕ) (α : ℝ) : ℝ := (2 : ℝ) ^ ((multiDeg k : ℝ) - α - 2)

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem two_rpow_natCast_mul (a n : ℕ) : (2 : ℝ) ^ ((a : ℝ) * n) = ((2 : ℝ) ^ n) ^ a := by
  rw [mul_comm, Real.rpow_mul_natCast (by norm_num), Real.rpow_natCast]

theorem two_rpow_neg_two_mul (n : ℕ) : (2 : ℝ) ^ (-2 * (n : ℝ)) = ((2 : ℝ) ^ n)⁻¹ ^ 2 := by
  have : (-2 : ℝ) * n = (-(n : ℝ)) * ((2 : ℕ) : ℝ) := by push_cast; ring
  rw [this, mul_comm, ← mul_comm, Real.rpow_mul_natCast (by norm_num), Real.rpow_neg (by norm_num),
    Real.rpow_natCast]

theorem derivShellRatio_nonneg (k : Fin 4 →₀ ℕ) (α : ℝ) : 0 ≤ derivShellRatio k α :=
  Real.rpow_nonneg (by norm_num) _

theorem derivShellRatio_lt_one {k : Fin 4 →₀ ℕ} {α : ℝ} (hk : (multiDeg k : ℝ) < α + 2) :
    derivShellRatio k α < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem two_rpow_deriv_mul_nat (k : Fin 4 →₀ ℕ) (α : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (((multiDeg k : ℝ) - α - 2) * n) = derivShellRatio k α ^ n := by
  rw [derivShellRatio, Real.rpow_mul_natCast (by norm_num)]

end RegularityStructures

end
