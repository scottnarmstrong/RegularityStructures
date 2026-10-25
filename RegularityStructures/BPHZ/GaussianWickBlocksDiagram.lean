/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickBlocksList
public import RegularityStructures.BPHZ.GaussianWickDiagram
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The diagram formula as a list recursion

The expectation of a product of Wick monomials is the matching sum, over all positions, of the
weight `blockWeight C` which vanishes on pairs inside a single block
(`integral_prod_wickMonomial_eq_matchingSum`).  For an explicit strictly increasing list of all
positions it is evaluated by the list recursion `listMatchSum`
(`integral_prod_wickMonomial_eq_listMatchSum`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {n r : ℕ}

/-- The pair weight on positions: the covariance of the letters, and `0` inside one block. -/
def blockWeight (C : Fin n → Fin n → ℝ) (L : Fin r → List (Fin n)) (c d : WickPosition L) : ℝ :=
  if c.block = d.block then 0 else C c.letter d.letter

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

variable {n r : ℕ}

theorem matchingSum_blockWeight_eq (C : Fin n → Fin n → ℝ) (L : Fin r → List (Fin n)) :
    matchingSum (blockWeight C L) (Finset.univ : Finset (WickPosition L)) =
      ∑ ρ ∈ (perfectMatchings (WickPosition L)).filter
          (fun ρ => ∀ c, (ρ c).block ≠ c.block),
        ∏ c ∈ Finset.univ.filter fun c => c < ρ c, C c.letter (ρ c).letter := by
  classical
  rw [Finset.sum_filter]
  unfold matchingSum perfectMatchings
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hρ' := mem_perfectMatchings.1 (by simpa [perfectMatchings] using hρ)
  unfold matchingWeight
  split_ifs with hok
  · refine Finset.prod_congr (by ext; simp) fun c _ => ?_
    have := hok c
    simp [blockWeight, Ne.symm this]
  · push Not at hok
    obtain ⟨c, hc⟩ := hok
    have hne : ρ c ≠ c := hρ'.2 c
    have hρρ : ρ (ρ c) = c := hρ'.1 c
    rcases lt_or_gt_of_ne hne.symm with hlt | hlt
    · refine Finset.prod_eq_zero (i := c) (by simp [hlt]) ?_
      simp [blockWeight, hc]
    · refine Finset.prod_eq_zero (i := ρ c) (by simp [hρρ, hlt]) ?_
      simp [blockWeight, hc, hρρ]

/-- The diagram formula with the block weight. -/
theorem integral_prod_wickMonomial_eq_matchingSum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (h : IsCentredGaussianVector P X C) (L : Fin r → List (Fin n)) :
    ∫ ω, ∏ j, wickMonomial C (L j) (X ω) ∂P =
      matchingSum (blockWeight C L) (Finset.univ : Finset (WickPosition L)) := by
  rw [integral_prod_wickMonomial_eq_sum_matchings h L, matchingSum_blockWeight_eq]

/-- The diagram formula evaluated along a strictly increasing list enumerating all positions. -/
theorem integral_prod_wickMonomial_eq_listMatchSum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (h : IsCentredGaussianVector P X C) (L : Fin r → List (Fin n))
    (l : List (WickPosition L)) (hl : l.Pairwise (· < ·)) (hall : ∀ c, c ∈ l) :
    ∫ ω, ∏ j, wickMonomial C (L j) (X ω) ∂P = listMatchSum (blockWeight C L) l := by
  rw [integral_prod_wickMonomial_eq_matchingSum h L,
    ← matchingSum_toFinset_eq_listMatchSum _ l hl]
  congr 1
  ext c
  simp [hall c]

end RegularityStructures

end
