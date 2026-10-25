/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianMatchingsRecursion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Fin

/-!
# Matching sums over sorted lists

`listMatchSum W l` is the pairing recursion on a list: pair the head with each other entry and
recurse on the remaining entries.  For a strictly increasing list `l` it equals
`matchingSum W l.toFinset` (`matchingSum_toFinset_eq_listMatchSum`).  Unlike the `Finset`
recursion, `listMatchSum` unfolds by `simp` on explicit lists.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The pairing recursion on a list: the head is paired with each of the other entries in turn. -/
def listMatchSum {ι : Type*} (W : ι → ι → ℝ) : List ι → ℝ
  | [] => 1
  | x :: t => ∑ i : Fin t.length, W x t[i] * listMatchSum W (t.eraseIdx i)
termination_by l => l.length
decreasing_by
  have := i.2
  simp [List.length_eraseIdx_of_lt i.2]
  omega

/-- Remove each entry of a list in turn: the pairs `(y, rest)` with `y` an entry and `rest` the
other entries. -/
def picks {ι : Type*} : List ι → List (ι × List ι)
  | [] => []
  | y :: s => (y, s) :: (picks s).map fun p => (p.1, y :: p.2)

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*}

theorem listMatchSum_nil (W : ι → ι → ℝ) : listMatchSum W [] = 1 := by
  rw [listMatchSum]

theorem listMatchSum_cons (W : ι → ι → ℝ) (x : ι) (t : List ι) :
    listMatchSum W (x :: t) = ∑ i : Fin t.length, W x t[i] * listMatchSum W (t.eraseIdx i) := by
  rw [listMatchSum]

theorem sum_fin_eq_picks {ι : Type*} (g : ι → List ι → ℝ) :
    ∀ t : List ι, ∑ i : Fin t.length, g t[i] (t.eraseIdx i) = ((picks t).map fun p => g p.1 p.2).sum
  | [] => by simp [picks]
  | y :: s => by
    rw [picks, List.map_cons, List.sum_cons, List.map_map]
    have := sum_fin_eq_picks (fun z r => g z (y :: r)) s
    have h2 : ∑ i : Fin (y :: s).length, g (y :: s)[i] ((y :: s).eraseIdx ↑i) =
        g (y :: s)[(0 : Fin (s.length + 1))] ((y :: s).eraseIdx 0) +
        ∑ i : Fin s.length, g (y :: s)[i.succ] ((y :: s).eraseIdx ↑i.succ) :=
      Fin.sum_univ_succ (n := s.length) (fun i : Fin (s.length + 1) =>
        g (y :: s)[i] ((y :: s).eraseIdx ↑i))
    rw [h2]
    simp only [Fin.val_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ,
      Fin.getElem_fin, List.getElem_cons_succ, Fin.coe_ofNat_eq_mod]
    simp only [Function.comp_def]
    congr 1

theorem listMatchSum_cons_picks (W : ι → ι → ℝ) (x : ι) (t : List ι) :
    listMatchSum W (x :: t) = ((picks t).map fun p => W x p.1 * listMatchSum W p.2).sum := by
  rw [listMatchSum_cons]
  exact sum_fin_eq_picks (fun z r => W x z * listMatchSum W r) t

theorem length_lt_of_mem_picks : ∀ (t : List ι) (p : ι × List ι), p ∈ picks t →
    p.2.length + 1 = t.length
  | [], p, hp => by simp [picks] at hp
  | y :: s, p, hp => by
    rw [picks, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      have := length_lt_of_mem_picks s q hq
      simp [← this]

theorem picks_map {κ : Type*} (f : ι → κ) : ∀ t : List ι,
    picks (t.map f) = (picks t).map fun p => (f p.1, p.2.map f)
  | [] => by simp [picks]
  | y :: s => by
    simp [picks, picks_map f s, Function.comp_def]

/-- `listMatchSum` is invariant under relabelling the entries of the list. -/
theorem listMatchSum_map {κ : Type*} (W : ι → ι → ℝ) (W' : κ → κ → ℝ) (f : ι → κ)
    (hW : ∀ c d, W c d = W' (f c) (f d)) :
    ∀ (k : ℕ) (l : List ι), l.length = k → listMatchSum W l = listMatchSum W' (l.map f) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro l hl
  match l, hl with
  | [], _ => simp [listMatchSum_nil]
  | x :: t, hl =>
    rw [List.map_cons, listMatchSum_cons_picks, listMatchSum_cons_picks, picks_map,
      List.map_map]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    have hlen := length_lt_of_mem_picks t p hp
    simp only [Function.comp_apply]
    rw [hW, ih p.2.length (by simp at hl; omega) p.2 rfl]

variable [Fintype ι] [LinearOrder ι]

/-- For a strictly increasing list, `matchingSum` over its entries is `listMatchSum`. -/
theorem matchingSum_toFinset_eq_listMatchSum (W : ι → ι → ℝ) :
    ∀ (l : List ι), l.Pairwise (· < ·) → matchingSum W l.toFinset = listMatchSum W l := by
  suffices h : ∀ (k : ℕ) (l : List ι), l.length = k → l.Pairwise (· < ·) →
      matchingSum W l.toFinset = listMatchSum W l from fun l => h _ l rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro l hn hl
  match l, hn, hl with
  | [], _, _ => simp [matchingSum_empty, listMatchSum_nil]
  | x :: t, hn, hl =>
    rw [List.pairwise_cons] at hl
    obtain ⟨hx, ht⟩ := hl
    have hxt : x ∉ t := fun h => lt_irrefl _ (hx x h)
    have hnd : t.Nodup := ht.imp ne_of_lt
    have hmem : x ∈ (x :: t).toFinset := by simp
    have hmin : ∀ b ∈ (x :: t).toFinset, x ≤ b := by
      intro b hb
      rcases List.mem_cons.1 (List.mem_toFinset.1 hb) with rfl | h
      · exact le_rfl
      · exact (hx b h).le
    have herase : (x :: t).toFinset.erase x = t.toFinset := by
      ext b
      simp only [Finset.mem_erase, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact absurd h2 h1
        · exact h2
      · intro h
        exact ⟨fun h' => hxt (h' ▸ h), Or.inr h⟩
    rw [matchingSum_eq_sum_erase W hmem hmin, herase, listMatchSum_cons]
    refine (Finset.sum_nbij (fun i : Fin t.length => t[i]) ?_ ?_ ?_ ?_).symm
    · intro i _
      simp
    · intro i _ j _ h
      exact Fin.ext ((hnd.getElem_inj_iff).1 h)
    · intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (List.mem_toFinset.1 hb)
      exact ⟨⟨i, hi⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
    · intro i _
      have hfin : (t.eraseIdx i).toFinset = t.toFinset.erase t[i] := by
        rw [← hnd.erase_getElem i.1 i.2]
        ext b
        simp [hnd.mem_erase_iff]
      have hlen : (t.eraseIdx i).length < k := by
        simp [List.length_eraseIdx_of_lt i.2] at hn ⊢
        omega
      rw [← ih _ hlen (t.eraseIdx i) rfl (ht.sublist (List.eraseIdx_sublist _ _)), hfin]

end RegularityStructures

end
