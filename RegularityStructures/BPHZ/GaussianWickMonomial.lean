/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianMatchings
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Wick monomials

For a covariance `C` on `Fin n` and a word `l : List (Fin n)` the Wick monomial
`wickMonomial C l : (Fin n → ℝ) → ℝ` is given by the Hermite formula
`:∏ₐ x_{l a}: = ∑_{π} (-1)^{#pairs π} ∏_{pairs {a,b} of π} C_{l a, l b} ∏_{a fixed by π} x_{l a}`,
where `π` runs over the involutions of the positions `Fin l.length` (partial matchings: pairs are
`{c, π c}` with `c < π c`, unmatched positions are the fixed points).

Special cases: `wickMonomial C [i] x = x i`, `wickMonomial C [i, i] x = x i ^ 2 - C i i` and
`wickMonomial C [i, i, i] x = x i ^ 3 - 3 * C i i * x i`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- All involutions of `ι` (partial matchings: the non-fixed points are matched in pairs). -/
def involutions (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset (ι → ι) :=
  Finset.univ.filter fun π => ∀ a, π (π a) = a

open scoped Classical in
/-- The smaller elements `c < π c` of the pairs of the matching `π`; its cardinality is the number
of pairs. -/
def pairSet {ι : Type*} [Fintype ι] [LT ι] (π : ι → ι) : Finset ι :=
  Finset.univ.filter fun c => c < π c

/-- The unmatched positions of `π`. -/
def fixedSet {ι : Type*} [Fintype ι] [DecidableEq ι] (π : ι → ι) : Finset ι :=
  Finset.univ.filter fun c => π c = c

/-- The Wick monomial of a word `l` for the covariance `C` (Hermite formula over partial
matchings of the positions of `l`). -/
def wickMonomial {n : ℕ} (C : Fin n → Fin n → ℝ) (l : List (Fin n))
    (x : Fin n → ℝ) : ℝ :=
  ∑ π ∈ involutions (Fin l.length),
    (-1) ^ (pairSet π).card *
      (matchingWeight (fun a b => C (l.get a) (l.get b)) π * ∏ c ∈ fixedSet π, x (l.get c))

theorem matchingWeight_eq_prod_pairSet {ι : Type*} [Fintype ι] [LT ι] (W : ι → ι → ℝ)
    (π : ι → ι) : matchingWeight W π = ∏ c ∈ pairSet π, W c (π c) := rfl

end RegularityStructures

end
