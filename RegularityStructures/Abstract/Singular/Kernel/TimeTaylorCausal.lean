/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Kernel.TimeTaylorScaled
public import RegularityStructures.Abstract.Singular.Kernel.Vanish

/-!
# Time-Taylor remainder: exact constants and causality of the subtracted terms
-/

public section

open scoped ContDiff

namespace RegularityStructures

variable {N : ℕ}

/-- Version of `exists_isScaledTest_shellTimeTaylorRem` with the constant
`C (x₁ 4^n)^m (2^n)^{|k|_𝔰 + 3}` itself (valid when it is positive, i.e. `m = 0` or `x₁ > 0`). -/
theorem exists_isScaledTest_shellTimeTaylorRem_const {h : ParabolicSpace → ℝ}
    (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ParabolicSpace, 0 ≤ x.1 →
      x.1 ≤ (((2 : ℝ) ^ n)⁻¹) ^ 2 → 0 < (x.1 * 4 ^ n) ^ m →
      IsScaledTest (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y) -
          ∑ j ∈ Finset.range m, (x.1 ^ j / (Nat.factorial j : ℝ)) *
            lineIter (multiDirs (k + Finsupp.single 0 j)) (scaledShell h n) ((0, x.2) - y))
        x (2 * ((2 : ℝ) ^ n)⁻¹) (C * (x.1 * 4 ^ n) ^ m * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3)) := by
  obtain ⟨C, hC, hmain⟩ := exists_isScaledTest_shellTimeTaylorRem hh k m
  refine ⟨C, hC, fun n hn x hx0 hx1 hpos => hmain n hn x hx0 hx1 _ ?_ le_rfl⟩
  positivity

/-- Each subtracted term `y ↦ D^{k'} K_n((0, x₂) - y)` vanishes for `y₁ ≥ 0` if the profile is
causal. -/
theorem lineIter_multiDirs_scaledShell_projection_eq_zero {h : ParabolicSpace → ℝ}
    (hh : ContDiff ℝ ∞ h) (h0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)
    (n : ℕ) (x₂ : Fin 3 → ℝ) {y : ParabolicSpace} (hy : 0 ≤ y.1) :
    lineIter (multiDirs k) (scaledShell h n) (((0 : ℝ), x₂) - y) = 0 :=
  lineIter_multiDirs_scaledShell_sub_eq_zero hh h0 k n (x := ((0 : ℝ), x₂)) hy

end RegularityStructures

end
