/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickBlocksDiagram
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Pairwise

/-!
# The sorted list of all positions

`allPositions L` lists the positions of the words `L j` in increasing order, block by block.
It is strictly increasing and contains every position, so the diagram formula can be evaluated
along it (`integral_prod_wickMonomial_eq_listMatchSum_allPositions`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace WickPosition

variable {n r : ℕ}

/-- All positions of the words `L j`, in increasing order. -/
def allPositions (L : Fin r → List (Fin n)) : List (WickPosition L) :=
  (List.finRange r).flatMap fun j => (List.finRange (L j).length).map (mk j)

end WickPosition

/-- The letters of the words `L j`, tagged with the index `j` of their word. -/
def taggedLetters {n r : ℕ} (L : Fin r → List (Fin n)) : List (ℕ × Fin n) :=
  (List.finRange r).flatMap fun j => (L j).map fun x => ((j : ℕ), x)

/-- The pair weight on tagged letters: `0` inside one word, else the covariance. -/
def taggedWeight {n : ℕ} (C : Fin n → Fin n → ℝ) (p q : ℕ × Fin n) : ℝ :=
  if p.1 = q.1 then 0 else C p.2 q.2

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

namespace WickPosition

variable {n r : ℕ} {L : Fin r → List (Fin n)}

theorem mk_lt_mk_of_lt {j k : Fin r} (hjk : j < k) (a : Fin (L j).length) (b : Fin (L k).length) :
    (mk j a : WickPosition L) < mk k b := by
  show toLex (((j : Fin r) : ℕ), (a : ℕ)) < toLex (((k : Fin r) : ℕ), (b : ℕ))
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl hjk

theorem pairwise_allPositions (L : Fin r → List (Fin n)) :
    (allPositions L).Pairwise (· < ·) := by
  unfold allPositions
  rw [List.pairwise_flatMap]
  refine ⟨fun j _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp fun {a b} h => mk_lt_mk_iff.2 h
  · refine (List.pairwise_lt_finRange r).imp fun {j k} hjk => ?_
    intro x hx y hy
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
    exact mk_lt_mk_of_lt hjk a b

theorem mem_allPositions (L : Fin r → List (Fin n)) (c : WickPosition L) :
    c ∈ allPositions L := by
  obtain ⟨j, a⟩ := c
  unfold allPositions
  exact List.mem_flatMap.2 ⟨j, List.mem_finRange j,
    List.mem_map.2 ⟨a, List.mem_finRange a, rfl⟩⟩

end WickPosition

/-- The diagram formula evaluated along the list of all positions. -/
theorem integral_prod_wickMonomial_eq_listMatchSum_allPositions {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n r : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (h : IsCentredGaussianVector P X C) (L : Fin r → List (Fin n)) :
    ∫ ω, ∏ j, wickMonomial C (L j) (X ω) ∂P =
      listMatchSum (blockWeight C L) (WickPosition.allPositions L) :=
  integral_prod_wickMonomial_eq_listMatchSum h L _ (WickPosition.pairwise_allPositions L)
    (WickPosition.mem_allPositions L)

variable {n r : ℕ} in
theorem map_allPositions (L : Fin r → List (Fin n)) :
    (WickPosition.allPositions L).map (fun c => ((c.block : ℕ), c.letter)) = taggedLetters L := by
  unfold WickPosition.allPositions taggedLetters
  rw [List.map_flatMap]
  refine List.flatMap_congr fun j _ => ?_
  rw [List.map_map]
  have : ((fun c : WickPosition L => ((c.block : ℕ), c.letter)) ∘ WickPosition.mk j) =
      (fun x => ((j : ℕ), x)) ∘ (L j).get := rfl
  rw [this, ← List.map_map, List.map_get_finRange]

/-- The diagram formula for words `L j`, evaluated by the list recursion on the tagged letters. -/
theorem integral_prod_wickMonomial_eq_listMatchSum_tagged {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n r : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (h : IsCentredGaussianVector P X C) (L : Fin r → List (Fin n)) :
    ∫ ω, ∏ j, wickMonomial C (L j) (X ω) ∂P =
      listMatchSum (taggedWeight C) (taggedLetters L) := by
  rw [integral_prod_wickMonomial_eq_listMatchSum_allPositions h L,
    listMatchSum_map (blockWeight C L) (taggedWeight C)
      (fun c : WickPosition L => ((c.block : ℕ), c.letter))
      (fun c d => by
        simp only [blockWeight, taggedWeight, Fin.val_inj]) _ _ rfl, map_allPositions]

end RegularityStructures

end
