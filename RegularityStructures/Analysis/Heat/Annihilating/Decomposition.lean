/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# The modified decomposition `G = ∑ annShell + annRemainder`

Smoothness, support, the telescoping identity
`∑_{n<M} annShell N n = ∑_{n<M} heatShell n - ψ + (2^M)^3 ψ(S^{2^M} ·)`, the decomposition of the
heat kernel, and Assumption 5.1 with `β = 2` for `annShell N`.

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem scaledShell_zero (h : ParabolicSpace → ℝ) (z : ParabolicSpace) : scaledShell h 0 z = h z := by
  simp [scaledShell]

theorem exists_inv_pow_lt {z : ParabolicSpace} (hz : z ≠ 0) :
    ∃ M : ℕ, (2 : ℝ)⁻¹ ^ M < parabolicNorm z := by
  have hpos : 0 < parabolicNorm z :=
    lt_of_lt_of_le (smoothParabolicNorm_pos hz) (smoothParabolicNorm_le_parabolicNorm z)
  exact exists_pow_lt_of_lt_one hpos (by norm_num)

end RegularityStructures

end
