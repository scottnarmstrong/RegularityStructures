/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickMonomial
public import RegularityStructures.BPHZ.GaussianIsserlis
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Merging and splitting matchings

If `π` is a partial matching and `ρ'` is a matching of the unmatched positions of `π`, then
`matchMerge π ρ'` is the matching with the pairs of both.  Conversely a perfect matching `ρ` and a
set `S` of (smaller elements of) pairs of `ρ` split into the sub-matching `restrictMatching ρ S`
formed by the pairs in `S` and the matching `complMatching ρ S` formed by the remaining pairs.
These are mutually inverse bijections, the combinatorial core of the diagram formula
(`GaussianWickDiagramIdentity`).
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι]

/-- The union of a partial matching `π` and a matching `ρ'` of its unmatched positions. -/
def matchMerge (π ρ' : ι → ι) (c : ι) : ι := if π c = c then ρ' c else π c

/-- The sub-matching of `ρ` formed by the pairs `{c, ρ c}` with `c ∈ S` (or `ρ c ∈ S`). -/
def restrictMatching (ρ : ι → ι) (S : Finset ι) (c : ι) : ι :=
  if c ∈ S ∨ ρ c ∈ S then ρ c else c

/-- The sub-matching of `ρ` formed by the pairs not meeting `S` (nor `ρ '' S`). -/
def complMatching (ρ : ι → ι) (S : Finset ι) (c : ι) : ι :=
  if c ∈ S ∨ ρ c ∈ S then c else ρ c

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*}

section Basic

variable [DecidableEq ι] {π ρ' : ι → ι}

theorem matchMerge_of_fixed {c : ι} (h : π c = c) : matchMerge π ρ' c = ρ' c := by
  simp only [matchMerge, h, ite_true]

theorem matchMerge_of_ne {c : ι} (h : π c ≠ c) : matchMerge π ρ' c = π c := by
  simp only [matchMerge, h, ite_false]

theorem restrictMatching_of_mem {ρ : ι → ι} {S : Finset ι} {c : ι} (h : c ∈ S ∨ ρ c ∈ S) :
    restrictMatching ρ S c = ρ c := by
  simp only [restrictMatching, h, ite_true]

theorem restrictMatching_of_not_mem {ρ : ι → ι} {S : Finset ι} {c : ι}
    (h : ¬ (c ∈ S ∨ ρ c ∈ S)) : restrictMatching ρ S c = c := by
  simp only [restrictMatching, h, ite_false]

theorem complMatching_of_mem {ρ : ι → ι} {S : Finset ι} {c : ι} (h : c ∈ S ∨ ρ c ∈ S) :
    complMatching ρ S c = c := by
  simp only [complMatching, h, ite_true]

theorem complMatching_of_not_mem {ρ : ι → ι} {S : Finset ι} {c : ι}
    (h : ¬ (c ∈ S ∨ ρ c ∈ S)) : complMatching ρ S c = ρ c := by
  simp only [complMatching, h, ite_false]

omit [DecidableEq ι] in
theorem apply_eq_self_of_disjoint (hρ : Function.Involutive ρ')
    (hd : ∀ a, ρ' a ≠ a ↔ π a = a) {a : ι} (ha : ρ' a ≠ a) : π (ρ' a) = ρ' a :=
  (hd (ρ' a)).1 (by rw [hρ a]; exact ha.symm)

theorem matchMerge_involutive (hπ : Function.Involutive π) (hρ : Function.Involutive ρ')
    (hd : ∀ a, ρ' a ≠ a ↔ π a = a) : Function.Involutive (matchMerge π ρ') := by
  intro c
  by_cases h : π c = c
  · have h1 : ρ' c ≠ c := (hd c).2 h
    have h2 := apply_eq_self_of_disjoint hρ hd h1
    rw [matchMerge_of_fixed h, matchMerge_of_fixed h2, hρ c]
  · rw [matchMerge_of_ne h, matchMerge_of_ne (by rw [hπ c]; exact fun h' => h h'.symm), hπ c]

theorem matchMerge_ne (hd : ∀ a, ρ' a ≠ a ↔ π a = a) (c : ι) : matchMerge π ρ' c ≠ c := by
  by_cases h : π c = c
  · rw [matchMerge_of_fixed h]
    exact (hd c).2 h
  · rw [matchMerge_of_ne h]
    exact h

theorem matchMerge_mem_perfectMatchings [Fintype ι] (hπ : Function.Involutive π)
    (hρ' : ρ' ∈ partialMatchings (fixedSet π)) :
    matchMerge π ρ' ∈ perfectMatchings ι := by
  rw [mem_partialMatchings] at hρ'
  have hd : ∀ a, ρ' a ≠ a ↔ π a = a := fun a => by simpa [fixedSet] using hρ'.2 a
  exact mem_perfectMatchings.2 ⟨matchMerge_involutive hπ hρ'.1 hd, matchMerge_ne hd⟩

end Basic

section Pairs

variable [DecidableEq ι] [Fintype ι] [LinearOrder ι] {π ρ' : ι → ι}

theorem pairSet_matchMerge (hd : ∀ a, ρ' a ≠ a ↔ π a = a) :
    pairSet (matchMerge π ρ') = pairSet π ∪ pairSet ρ' := by
  ext c
  simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  by_cases h : π c = c
  · rw [matchMerge_of_fixed h, h]
    simp
  · have h2 : ¬ c < ρ' c := fun hlt => h ((hd c).1 hlt.ne')
    rw [matchMerge_of_ne h]
    simp [h2]

omit [DecidableEq ι] in
theorem disjoint_pairSet (hd : ∀ a, ρ' a ≠ a ↔ π a = a) :
    Disjoint (pairSet π) (pairSet ρ') := by
  rw [Finset.disjoint_left]
  intro c h1 h2
  simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  exact h1.ne ((hd c).1 h2.ne').symm

theorem matchingWeight_matchMerge (hd : ∀ a, ρ' a ≠ a ↔ π a = a) (W : ι → ι → ℝ) :
    matchingWeight W (matchMerge π ρ') = matchingWeight W π * matchingWeight W ρ' := by
  rw [matchingWeight_eq_prod_pairSet, pairSet_matchMerge hd,
    Finset.prod_union (disjoint_pairSet hd), matchingWeight_eq_prod_pairSet,
    matchingWeight_eq_prod_pairSet]
  congr 1
  · refine Finset.prod_congr rfl fun c hc => ?_
    have : π c ≠ c := by
      simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc.ne'
    rw [matchMerge_of_ne this]
  · refine Finset.prod_congr rfl fun c hc => ?_
    have : π c = c := by
      simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact (hd c).1 hc.ne'
    rw [matchMerge_of_fixed this]

end Pairs

section Restrict

variable [DecidableEq ι] {ρ : ι → ι} {S : Finset ι}

theorem restrictMatching_involutive (hρ : Function.Involutive ρ) (S : Finset ι) :
    Function.Involutive (restrictMatching ρ S) := by
  intro c
  by_cases h : c ∈ S ∨ ρ c ∈ S
  · have h2 : ρ c ∈ S ∨ ρ (ρ c) ∈ S := by rw [hρ c]; exact h.symm
    rw [restrictMatching_of_mem h, restrictMatching_of_mem h2, hρ c]
  · rw [restrictMatching_of_not_mem h, restrictMatching_of_not_mem h]

theorem restrictMatching_block {B : Type*} (β : ι → B) (hρ : Function.Involutive ρ)
    (hS : ∀ c ∈ S, β (ρ c) = β c) (c : ι) : β (restrictMatching ρ S c) = β c := by
  by_cases h : c ∈ S ∨ ρ c ∈ S
  · rw [restrictMatching_of_mem h]
    rcases h with h | h
    · exact hS c h
    · have := hS _ h
      rw [hρ c] at this
      exact this.symm
  · rw [restrictMatching_of_not_mem h]

theorem pairSet_restrictMatching [Fintype ι] [LinearOrder ι] (hρ : Function.Involutive ρ)
    (hS : ∀ c ∈ S, c < ρ c) : pairSet (restrictMatching ρ S) = S := by
  ext c
  simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : c ∈ S ∨ ρ c ∈ S
  · rw [restrictMatching_of_mem h]
    constructor
    · intro hlt
      rcases h with h | h
      · exact h
      · have := hS _ h
        rw [hρ c] at this
        exact absurd hlt (lt_asymm this)
    · intro hc
      exact hS c hc
  · have hc : c ∉ S := fun hc => h (Or.inl hc)
    rw [restrictMatching_of_not_mem h]
    simp [hc]

theorem complMatching_mem [Fintype ι] (hρ : Function.Involutive ρ) (hne : ∀ c, ρ c ≠ c)
    (S : Finset ι) : complMatching ρ S ∈ partialMatchings (fixedSet (restrictMatching ρ S)) := by
  rw [mem_partialMatchings]
  refine ⟨fun c => ?_, fun c => ?_⟩
  · by_cases h : c ∈ S ∨ ρ c ∈ S
    · rw [complMatching_of_mem h, complMatching_of_mem h]
    · have h2 : ¬ (ρ c ∈ S ∨ ρ (ρ c) ∈ S) := by rw [hρ c]; tauto
      rw [complMatching_of_not_mem h, complMatching_of_not_mem h2, hρ c]
  · by_cases h : c ∈ S ∨ ρ c ∈ S
    · rw [complMatching_of_mem h]
      simp [fixedSet, restrictMatching_of_mem h, hne c]
    · rw [complMatching_of_not_mem h]
      simp [fixedSet, restrictMatching_of_not_mem h, hne c]

theorem matchMerge_restrictMatching (hne : ∀ c, ρ c ≠ c) (S : Finset ι) :
    matchMerge (restrictMatching ρ S) (complMatching ρ S) = ρ := by
  funext c
  by_cases h : c ∈ S ∨ ρ c ∈ S
  · rw [matchMerge_of_ne (by rw [restrictMatching_of_mem h]; exact hne c),
      restrictMatching_of_mem h]
  · rw [matchMerge_of_fixed (by rw [restrictMatching_of_not_mem h]),
      complMatching_of_not_mem h]

end Restrict

section Split

variable [DecidableEq ι] [Fintype ι] [LinearOrder ι] {π ρ' : ι → ι}

omit [DecidableEq ι] in
private theorem mem_or_apply_mem_pairSet (hπ : Function.Involutive π) {c : ι} (h : π c ≠ c) :
    c ∈ pairSet π ∨ π c ∈ pairSet π := by
  simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and, hπ c]
  rcases lt_or_gt_of_ne (Ne.symm h) with h4 | h4
  · exact Or.inl h4
  · exact Or.inr h4

private theorem not_mem_pairSet_of_fixed (hρ : Function.Involutive ρ')
    (hd : ∀ a, ρ' a ≠ a ↔ π a = a) {c : ι} (h : π c = c) :
    ¬ (c ∈ pairSet π ∨ matchMerge π ρ' c ∈ pairSet π) := by
  have h1 := (hd c).2 h
  have h2 := apply_eq_self_of_disjoint hρ hd h1
  rw [matchMerge_of_fixed h]
  simp [pairSet, h, h2]

theorem restrictMatching_matchMerge (hπ : Function.Involutive π) (hρ : Function.Involutive ρ')
    (hd : ∀ a, ρ' a ≠ a ↔ π a = a) :
    restrictMatching (matchMerge π ρ') (pairSet π) = π := by
  funext c
  by_cases h : π c = c
  · rw [restrictMatching_of_not_mem (not_mem_pairSet_of_fixed hρ hd h), h]
  · have h3 : c ∈ pairSet π ∨ matchMerge π ρ' c ∈ pairSet π := by
      rw [matchMerge_of_ne h]
      exact mem_or_apply_mem_pairSet hπ h
    rw [restrictMatching_of_mem h3, matchMerge_of_ne h]

theorem complMatching_matchMerge (hπ : Function.Involutive π) (hρ : Function.Involutive ρ')
    (hd : ∀ a, ρ' a ≠ a ↔ π a = a) :
    complMatching (matchMerge π ρ') (pairSet π) = ρ' := by
  funext c
  by_cases h : π c = c
  · rw [complMatching_of_not_mem (not_mem_pairSet_of_fixed hρ hd h), matchMerge_of_fixed h]
  · have h3 : c ∈ pairSet π ∨ matchMerge π ρ' c ∈ pairSet π := by
      rw [matchMerge_of_ne h]
      exact mem_or_apply_mem_pairSet hπ h
    have : ρ' c = c := by
      by_contra hc
      exact h ((hd c).1 hc)
    rw [complMatching_of_mem h3, this]

end Split

end RegularityStructures

end
