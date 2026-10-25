/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Generator
public import RegularityStructures.Analysis.Parabolic.Polynomial
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Regularising kernels on `ℝ⁴` (Hairer's Assumption 5.1)

A kernel `K(x, y)` "improves regularity by `β`" [Hai14, Assumption 5.1] if it decomposes as
`K = ∑_{n ≥ 0} K_n` with

* `K_n` smooth and supported in `{‖x − y‖_𝔰 ≤ 2^{-n}}`;
* `|D₁^k D₂^l K_n(x, y)| ≤ C 2^{(|𝔰| − β + |l|_𝔰 + |k|_𝔰) n}`, `|𝔰| = 5` ((5.4));
* `|∫ (x − y)^l D₂^k K_n(x, y) dx| ≤ C 2^{-βn}` and `|∫ (y − x)^l D₁^k K_n(x, y) dy| ≤ C 2^{-βn}`
  ((5.5));

and it annihilates polynomials up to order `r` if `∫ K_n(x, y) P(y) dy = 0` for all polynomials
`P` of parabolic degree `≤ r` [Hai14, Assumption 5.4].

Derivatives along a multi-index `k ∈ ℕ⁴` are iterated Fréchet derivatives along the coordinate
directions (`multiDirs k`, `k₀` copies of the time direction and `kᵢ` copies of the `i`-th space
direction); `D₁` and `D₂` act on the first and second argument of `K_n` respectively.

Source: [Hai14] = arXiv:1303.5113v4, §5.1, (5.3)–(5.6).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

/-- The coordinate directions of `ℝ⁴`: `0 ↦ (1, 0)`, `i + 1 ↦ (0, eᵢ)`. -/
def coordDir : Fin 4 → ParabolicSpace :=
  Fin.cases timeDir spaceDir

/-- The list of directions of the multi-index `k`: `k_j` copies of `coordDir j`. -/
def multiDirs (k : Fin 4 →₀ ℕ) : List ParabolicSpace :=
  (Finsupp.toMultiset k).toList.map coordDir

/-- The parabolic degree `|k|_𝔰 = 2k₀ + k₁ + k₂ + k₃` of a multi-index. -/
def multiDeg (k : Fin 4 →₀ ℕ) : ℕ := Finsupp.weight parabolicWeight k

end RegularityStructures

end

public section

namespace RegularityStructures

theorem coordDir_zero : coordDir 0 = timeDir := rfl

theorem coordDir_succ (i : Fin 3) : coordDir i.succ = spaceDir i := rfl

end RegularityStructures

end
