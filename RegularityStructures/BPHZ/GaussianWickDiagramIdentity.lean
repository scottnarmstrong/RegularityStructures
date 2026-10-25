/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickMerge
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The combinatorial identity behind the diagram formula

Let `β : ι → B` label the *blocks* of the positions `ι`.  A *block involution* is an involution
`π` of `ι` whose pairs lie inside blocks.  For a weight `W`,

`∑_{π block involution} (-1)^{#pairs π} * mw π * matchingSum W (fixed points of π)`
`  = ∑_{ρ perfect matching, no pair inside a block} mw ρ`,

where `mw` is `matchingWeight W` (`sum_blockInvolutions_matchingSum`).  The proof merges `π` with a
perfect matching of its fixed points into a perfect matching `ρ`, remembering the set `S` of pairs
of `ρ` coming from `π`; the sum over `S ⊆ {inner pairs of ρ}` of `(-1)^{|S|}` vanishes unless
`ρ` has no inner pair.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The involutions of `ι` all of whose pairs lie inside a block of `β`. -/
def blockInvolutions {ι B : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq B] (β : ι → B) :
    Finset (ι → ι) :=
  (involutions ι).filter fun π => ∀ c, β (π c) = β c

open scoped Classical in
/-- The (smaller elements of the) pairs of `ρ` lying inside a block of `β`. -/
def innerPairSet {ι B : Type*} [Fintype ι] [LT ι] (β : ι → B) (ρ : ι → ι) : Finset ι :=
  Finset.univ.filter fun c => c < ρ c ∧ β (ρ c) = β c

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι B : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [DecidableEq B]

omit [LinearOrder ι] in
theorem mem_involutions {π : ι → ι} : π ∈ involutions ι ↔ Function.Involutive π := by
  simp [involutions, Function.Involutive]

omit [LinearOrder ι] in
theorem mem_blockInvolutions {β : ι → B} {π : ι → ι} :
    π ∈ blockInvolutions β ↔ Function.Involutive π ∧ ∀ c, β (π c) = β c := by
  simp [blockInvolutions, mem_involutions]

omit [DecidableEq ι] [DecidableEq B] in
theorem mem_innerPairSet {β : ι → B} {ρ : ι → ι} {c : ι} :
    c ∈ innerPairSet β ρ ↔ c < ρ c ∧ β (ρ c) = β c := by
  simp [innerPairSet]

omit [DecidableEq ι] [DecidableEq B] in
theorem innerPairSet_eq_empty_iff {β : ι → B} {ρ : ι → ι} (hρ : ρ ∈ perfectMatchings ι) :
    innerPairSet β ρ = ∅ ↔ ∀ c, β (ρ c) ≠ β c := by
  rw [mem_perfectMatchings] at hρ
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h c hc
    rcases lt_or_gt_of_ne (hρ.2 c).symm with hlt | hlt
    · exact h c (mem_innerPairSet.2 ⟨hlt, hc⟩)
    · refine h (ρ c) (mem_innerPairSet.2 ⟨?_, ?_⟩)
      · rwa [hρ.1 c]
      · rw [hρ.1 c, hc]
  · intro h c hc
    exact h c (mem_innerPairSet.1 hc).2

omit [Fintype ι] [LinearOrder ι] in
private theorem sum_neg_one_pow_card_powerset (T : Finset ι) :
    ∑ S ∈ T.powerset, (-1 : ℝ) ^ S.card = if T = ∅ then 1 else 0 := by
  have h := congrArg (Int.cast : ℤ → ℝ) (Finset.sum_powerset_neg_one_pow_card (x := T))
  push_cast at h
  rw [h]

/-- **The merging bijection.** -/
theorem sum_blockInvolutions_matchingSum (β : ι → B) (W : ι → ι → ℝ) :
    ∑ π ∈ blockInvolutions β, (-1 : ℝ) ^ (pairSet π).card *
        (matchingWeight W π * matchingSum W (fixedSet π)) =
      ∑ ρ ∈ (perfectMatchings ι).filter (fun ρ => ∀ c, β (ρ c) ≠ β c), matchingWeight W ρ := by
  have hL : ∑ π ∈ blockInvolutions β, (-1 : ℝ) ^ (pairSet π).card *
        (matchingWeight W π * matchingSum W (fixedSet π)) =
      ∑ x ∈ (blockInvolutions β).sigma (fun π => partialMatchings (fixedSet π)),
        (-1 : ℝ) ^ (pairSet x.1).card * (matchingWeight W x.1 * matchingWeight W x.2) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [matchingSum, Finset.mul_sum, Finset.mul_sum]
  have hR : ∑ ρ ∈ (perfectMatchings ι).filter (fun ρ => ∀ c, β (ρ c) ≠ β c), matchingWeight W ρ =
      ∑ y ∈ (perfectMatchings ι).sigma (fun ρ => (innerPairSet β ρ).powerset),
        (-1 : ℝ) ^ y.2.card * matchingWeight W y.1 := by
    rw [Finset.sum_sigma, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    dsimp only
    rw [← Finset.sum_mul, sum_neg_one_pow_card_powerset]
    by_cases h : ∀ c, β (ρ c) ≠ β c
    · simp [h, (innerPairSet_eq_empty_iff hρ).2 h]
    · have h' : innerPairSet β ρ ≠ ∅ := fun h' => h ((innerPairSet_eq_empty_iff hρ).1 h')
      simp [h, h']
  rw [hL, hR]
  refine Finset.sum_bij' (fun x _ => ⟨matchMerge x.1 x.2, pairSet x.1⟩)
    (fun y _ => ⟨restrictMatching y.1 y.2, complMatching y.1 y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨π, ρ'⟩ hx
    rw [Finset.mem_sigma, mem_blockInvolutions] at hx
    obtain ⟨⟨hπ, hβ⟩, hρ'⟩ := hx
    refine Finset.mem_sigma.2 ⟨matchMerge_mem_perfectMatchings hπ hρ', ?_⟩
    rw [Finset.mem_powerset]
    intro c hc
    change c ∈ pairSet π at hc
    have hlt : c < π c := by simpa [pairSet] using hc
    change c ∈ innerPairSet β (matchMerge π ρ')
    rw [mem_innerPairSet, matchMerge_of_ne hlt.ne']
    exact ⟨hlt, hβ c⟩
  · rintro ⟨ρ, S⟩ hy
    rw [Finset.mem_sigma, Finset.mem_powerset] at hy
    obtain ⟨hρ, hS⟩ := hy
    have hρ' := mem_perfectMatchings.1 hρ
    refine Finset.mem_sigma.2 ⟨mem_blockInvolutions.2 ⟨restrictMatching_involutive hρ'.1 S,
      restrictMatching_block β hρ'.1 fun c hc => (mem_innerPairSet.1 (hS hc)).2⟩,
      complMatching_mem hρ'.1 hρ'.2 S⟩
  · rintro ⟨π, ρ'⟩ hx
    rw [Finset.mem_sigma, mem_blockInvolutions, mem_partialMatchings] at hx
    obtain ⟨⟨hπ, hβ⟩, hρ, hd⟩ := hx
    have hd' : ∀ a, ρ' a ≠ a ↔ π a = a := fun a => by simpa [fixedSet] using hd a
    refine Sigma.ext (restrictMatching_matchMerge hπ hρ hd') (heq_of_eq ?_)
    exact complMatching_matchMerge hπ hρ hd'
  · rintro ⟨ρ, S⟩ hy
    rw [Finset.mem_sigma, Finset.mem_powerset] at hy
    obtain ⟨hρ, hS⟩ := hy
    have hρ' := mem_perfectMatchings.1 hρ
    refine Sigma.ext (matchMerge_restrictMatching hρ'.2 S) (heq_of_eq ?_)
    exact pairSet_restrictMatching hρ'.1 fun c hc => (mem_innerPairSet.1 (hS hc)).1
  · rintro ⟨π, ρ'⟩ hx
    rw [Finset.mem_sigma, mem_partialMatchings] at hx
    obtain ⟨-, -, hd⟩ := hx
    have hd' : ∀ a, ρ' a ≠ a ↔ π a = a := fun a => by simpa [fixedSet] using hd a
    simp only
    rw [matchingWeight_matchMerge hd']

end RegularityStructures

end
