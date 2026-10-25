/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Shell

/-!
# Pairing of a distribution with a heat shell

For `Λ ∈ parabolicSemigroup.distributions` with `|Λ_u(y)| ≤ C u^{α/4}` (`0 < u ≤ 1`) and
`-2 < α`, the pairing against the `n`-th shell satisfies
`|⟨Λ, heatShell n (x - ·)⟩| ≤ c₀ C 2^{-(α+2) n}` (`abs_pairing_heatShell_le`), with `c₀` depending
only on `α`.  This is the `n`-th term of the Schauder estimate [Hai14, Section 5], with the kernel
regularising of order `β = 2`.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem two_inv_pow_rpow (n : ℕ) (α : ℝ) :
    ((2 : ℝ)⁻¹ ^ n) ^ α = (2 : ℝ) ^ (-α * n) := by
  have : (2 : ℝ)⁻¹ ^ n = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  rw [this, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

end RegularityStructures

end
