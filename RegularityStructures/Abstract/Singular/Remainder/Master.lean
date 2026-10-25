/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Kernel
public import RegularityStructures.Abstract.Singular.Remainder.Defs

/-!
# The reconstruction of the pieces of a remainder kernel

For a remainder kernel `Φ` with constant `B`, `x₀ ≤ T ≤ 1`, and `Φ(x − y) = 0` for `y₀ > T`, the
lattice approximations of every piece `Φ(x − ·) χ_{3,j}` converge, and
`|⟨R f, Φ(x − ·) χ_{3,j}⟩| ≤ C K₀ Cf B (1 + |x' − z_j'|²)^{-3}`, for `j₀` in the time window
`-1 ≤ j₀ ≤ 63`; all other pieces have zero reconstruction (`exists_remPiece_le`).
Summing over `j` gives `Summable` and `|M.remPairing f Φ(x − ·)| ≤ C K₀ Cf B`
(`exists_abs_remPairing_le`).
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem remPiece_vanish_of_not_mem_window {Φ : ParabolicSpace → ℝ} {x : ParabolicSpace}
    {T : ℝ} (hT : T ≤ 1) (hΦT : ∀ y : ParabolicSpace, T < y.1 → Φ (x - y) = 0)
    {j : LatticeIndex} (hj : j.1 ∉ Finset.Icc (-1 : ℤ) 63) :
    ∀ w : ParabolicSpace, 0 ≤ w.1 → Φ (x - w) * latticeCell 3 j w = 0 := by
  intro w hw
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  obtain ⟨⟨hlo, hhi⟩, -⟩ := latticeCell_ne_zero h2
  rw [latticePoint_fst] at hlo hhi
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
  rcases hj with hj | hj
  · have : (j.1 : ℝ) ≤ -2 := by exact_mod_cast (by omega : j.1 ≤ -2)
    nlinarith
  · have : (64 : ℝ) ≤ j.1 := by exact_mod_cast (by omega : 64 ≤ j.1)
    refine h1 (hΦT w ?_)
    nlinarith

end RegularityStructures

end
