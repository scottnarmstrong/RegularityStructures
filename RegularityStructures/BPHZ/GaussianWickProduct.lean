/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickPositions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Products of Wick monomials as sums over block involutions

`∏ⱼ wickMonomial C (L j) x` is the sum, over the involutions of all positions that preserve every
block, of `(-1)^{#pairs} * ∏_{pairs} C * ∏_{unmatched} x`
(`prod_wickMonomial_eq_sum_blockInvolutions`).  The block-wise product of involutions of the
individual words is a bijection onto these block involutions.
-/

@[expose] public section

namespace RegularityStructures

namespace WickPosition

variable {n r : ℕ} {L : Fin r → List (Fin n)}

/-- The involution of all positions obtained by acting by `p j` in the block `j`. -/
def blockwise (p : ∀ j, Fin (L j).length → Fin (L j).length) (c : WickPosition L) :
    WickPosition L :=
  ⟨c.1, p c.1 c.2⟩

end WickPosition

end RegularityStructures

end

public section

namespace RegularityStructures

namespace WickPosition

variable {n r : ℕ} {L : Fin r → List (Fin n)}

theorem mk_lt_mk_iff {j : Fin r} {a b : Fin (L j).length} :
    (mk j a : WickPosition L) < mk j b ↔ a < b := by
  show toLex (((j : Fin r) : ℕ), (a : ℕ)) < toLex (((j : Fin r) : ℕ), (b : ℕ)) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  simp only [lt_self_iff_false, true_and, false_or]
  exact Iff.rfl

theorem mk_inj {j : Fin r} {a b : Fin (L j).length} :
    (mk j a : WickPosition L) = mk j b ↔ a = b := by
  exact ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => by rw [h]⟩

theorem blockwise_involutive {p : ∀ j, Fin (L j).length → Fin (L j).length}
    (hp : ∀ j, Function.Involutive (p j)) : Function.Involutive (blockwise p) := by
  rintro ⟨j, a⟩
  show mk j (p j (p j a)) = mk j a
  rw [hp j a]

section Factor

variable (p : ∀ j, Fin (L j).length → Fin (L j).length)

theorem pairSet_blockwise :
    pairSet (blockwise p) =
      (Finset.univ.sigma fun j => pairSet (p j) : Finset (WickPosition L)) := by
  ext ⟨j, a⟩
  simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma]
  exact mk_lt_mk_iff

theorem fixedSet_blockwise :
    fixedSet (blockwise p) =
      (Finset.univ.sigma fun j => fixedSet (p j) : Finset (WickPosition L)) := by
  ext ⟨j, a⟩
  simp only [fixedSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma]
  exact mk_inj

theorem card_pairSet_blockwise :
    (pairSet (blockwise p)).card = ∑ j, (pairSet (p j)).card := by
  rw [pairSet_blockwise, Finset.card_sigma]

theorem prod_pairSet_blockwise (f : WickPosition L → ℝ) :
    ∏ c ∈ pairSet (blockwise p), f c = ∏ j, ∏ a ∈ pairSet (p j), f (mk j a) := by
  rw [pairSet_blockwise, Finset.prod_sigma]
  rfl

theorem prod_fixedSet_blockwise (f : WickPosition L → ℝ) :
    ∏ c ∈ fixedSet (blockwise p), f c = ∏ j, ∏ a ∈ fixedSet (p j), f (mk j a) := by
  rw [fixedSet_blockwise, Finset.prod_sigma]
  rfl

end Factor

theorem blockwise_injective : Function.Injective (blockwise (L := L)) := by
  intro p q h
  funext j a
  have := congrFun h (mk j a)
  exact eq_of_heq (Sigma.mk.inj this).2

theorem blockwise_block (p : ∀ j, Fin (L j).length → Fin (L j).length) (c : WickPosition L) :
    (blockwise p c).block = c.block := rfl

theorem exists_blockwise_eq {π : WickPosition L → WickPosition L}
    (hπ : Function.Involutive π) (hβ : ∀ c, (π c).block = c.block) :
    ∃ p : ∀ j, Fin (L j).length → Fin (L j).length,
      (∀ j, Function.Involutive (p j)) ∧ blockwise p = π := by
  have hex : ∀ (j : Fin r) (a : Fin (L j).length), ∃ b, π (mk j a) = mk j b := by
    intro j a
    have h := hβ (mk j a)
    revert h
    rcases π (mk j a) with ⟨j', b⟩
    intro h
    obtain rfl : j' = j := h
    exact ⟨b, rfl⟩
  choose p hp using hex
  have hbw : blockwise p = π := by
    funext c
    obtain ⟨j, a⟩ := c
    exact (hp j a).symm
  refine ⟨p, fun j a => ?_, hbw⟩
  have h1 := hπ (mk j a)
  rw [hp j a, hp j (p j a)] at h1
  exact (mk_inj.1 h1)

end WickPosition

open WickPosition in
/-- **Products of Wick monomials as sums over block involutions.** -/
theorem prod_wickMonomial_eq_sum_blockInvolutions {n r : ℕ} (C : Fin n → Fin n → ℝ)
    (L : Fin r → List (Fin n)) (x : Fin n → ℝ) :
    ∏ j, wickMonomial C (L j) x =
      ∑ π ∈ blockInvolutions (fun c : WickPosition L => c.block),
        (-1 : ℝ) ^ (pairSet π).card *
          (matchingWeight (fun a b : WickPosition L => C a.letter b.letter) π *
            ∏ c ∈ fixedSet π, x c.letter) := by
  unfold wickMonomial
  rw [Finset.prod_univ_sum]
  refine Finset.sum_bij (fun p _ => blockwise p) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Fintype.mem_piFinset] at hp
    exact mem_blockInvolutions.2 ⟨blockwise_involutive fun j => mem_involutions.1 (hp j),
      blockwise_block p⟩
  · intro p _ q _ h
    exact blockwise_injective h
  · intro π hπ
    rw [mem_blockInvolutions] at hπ
    obtain ⟨p, hp, hbw⟩ := exists_blockwise_eq hπ.1 hπ.2
    exact ⟨p, Fintype.mem_piFinset.2 fun j => mem_involutions.2 (hp j), hbw⟩
  · intro p hp
    rw [Finset.prod_mul_distrib, card_pairSet_blockwise, matchingWeight_eq_prod_pairSet,
      prod_pairSet_blockwise, prod_fixedSet_blockwise, ← Finset.prod_pow_eq_pow_sum,
      Finset.prod_mul_distrib]
    congr 2

end RegularityStructures

end
