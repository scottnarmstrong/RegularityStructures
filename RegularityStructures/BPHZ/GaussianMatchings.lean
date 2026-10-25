/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

/-!
# Partial matchings of a finite linearly ordered type

A *partial matching* of `ι` is an involution `π : ι → ι`; its *matched set* is the set of points
that `π` moves, its *pairs* are the sets `{c, π c}` with `π c ≠ c`, and its fixed points are the
unmatched points.  For `s : Finset ι`, `partialMatchings s` is the set of involutions whose matched
set is exactly `s`; for `s = univ` these are the perfect matchings, i.e. the fixed-point-free
involutions.

For a weight `W : ι → ι → ℝ`, `matchingWeight W π = ∏_{c < π c} W c (π c)` is the product over the
pairs of `π` (each pair is counted once, oriented increasingly) and
`matchingSum W s = ∑_{π ∈ partialMatchings s} matchingWeight W π`.

The main result is the recursion obtained by pairing the minimum `a` of `s` with each other element
`b` of `s`: `matchingSum W s = ∑_{b ∈ s \ {a}} W a b * matchingSum W (s \ {a, b})`
(`matchingSum_eq_sum_erase`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

open scoped Classical in
/-- The involutions of `ι` whose set of non-fixed points is exactly `s`. For `s = univ` these are
the perfect matchings of `ι`. -/
def partialMatchings {ι : Type*} [Fintype ι] (s : Finset ι) : Finset (ι → ι) :=
  Finset.univ.filter fun π => Function.Involutive π ∧ ∀ a, π a ≠ a ↔ a ∈ s

open scoped Classical in
/-- The product of the weights of the pairs `{c, π c}` (with `c < π c`) of the matching `π`. -/
def matchingWeight {ι : Type*} [Fintype ι] [LT ι] (W : ι → ι → ℝ) (π : ι → ι) : ℝ :=
  ∏ c ∈ Finset.univ.filter fun c => c < π c, W c (π c)

/-- The sum of the weights over all partial matchings with matched set `s`. -/
def matchingSum {ι : Type*} [Fintype ι] [LT ι] (W : ι → ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ π ∈ partialMatchings s, matchingWeight W π

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι]

theorem mem_partialMatchings {s : Finset ι} {π : ι → ι} :
    π ∈ partialMatchings s ↔ Function.Involutive π ∧ ∀ a, π a ≠ a ↔ a ∈ s := by
  simp [partialMatchings]

theorem partialMatchings_empty : partialMatchings (∅ : Finset ι) = {id} := by
  ext π
  rw [mem_partialMatchings, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    funext a
    by_contra hne
    exact absurd ((h a).1 hne) (by simp)
  · rintro rfl
    exact ⟨fun _ => rfl, by simp⟩

theorem matchingWeight_id [Preorder ι] (W : ι → ι → ℝ) : matchingWeight W (id : ι → ι) = 1 := by
  simp [matchingWeight]

theorem matchingSum_empty [Preorder ι] (W : ι → ι → ℝ) : matchingSum W (∅ : Finset ι) = 1 := by
  simp [matchingSum, partialMatchings_empty, matchingWeight_id]

end RegularityStructures

end
