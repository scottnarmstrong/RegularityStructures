/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGlobalGammaRightIncrement
public import RegularityStructures.Probability.ModelKolmogorovGlobalSourceMoments
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Annealed right-endpoint Gamma increment moments

This is an ingredient of the Kolmogorov criterion for models [Hai14, Theorem 10.7]. The model
cocycle at the right endpoint is combined with the global coordinate source bounds. The finite
intermediate-degree products remain explicit, and the two-model theorem is supplied by the
corresponding difference reduction elsewhere.
-/

public section

open MeasureTheory Classical
open scoped ENNReal NNReal

namespace RegularityStructures

/- The two-model right Chen increment retains only strictly intermediate degrees. -/
theorem gammaMap_single_diff_right_increment_lower
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
    {μ : Measure E} {𝒯 : RegularityStructure ι} {Q : RegularisingSemigroup E μ}
    (M Mbar : Model 𝒯 Q) (x y z : E) {i j : ι} (hji : 𝒯.deg j < 𝒯.deg i) :
    (M.gammaMap x z (Pi.single i 1) j - Mbar.gammaMap x z (Pi.single i 1) j) -
      (M.gammaMap x y (Pi.single i 1) j - Mbar.gammaMap x y (Pi.single i 1) j) =
      (M.gammaMap y z (Pi.single i 1) j - Mbar.gammaMap y z (Pi.single i 1) j) +
        ∑ k ∈ Finset.univ.filter
          (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i),
          ((M.gammaMap y z (Pi.single i 1) k -
              Mbar.gammaMap y z (Pi.single i 1) k) *
            M.gammaMap x y (Pi.single k 1) j +
          Mbar.gammaMap y z (Pi.single i 1) k *
            (M.gammaMap x y (Pi.single k 1) j -
              Mbar.gammaMap x y (Pi.single k 1) j)) := by
  classical
  let L := Finset.univ.filter (fun k => 𝒯.deg k < 𝒯.deg i)
  let B := Finset.univ.filter
    (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i)
  let T : ι → ℝ := fun k =>
    ((M.gammaMap y z (Pi.single i 1) k - Mbar.gammaMap y z
        (Pi.single i 1) k) * M.gammaMap x y (Pi.single k 1) j +
      (Mbar.gammaMap y z (Pi.single i 1) k -
        (Pi.single i 1 : ι → ℝ) k) *
        (M.gammaMap x y (Pi.single k 1) j -
          Mbar.gammaMap x y (Pi.single k 1) j))
  have hhigh : (∑ k ∈ Finset.univ.filter (fun k => ¬𝒯.deg k < 𝒯.deg i), T k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hki : k = i
    · subst k
      simp [T, M.gammaMap_single_apply_self, Mbar.gammaMap_single_apply_self]
    · have hz := M.gammaMap_single_apply_of_le z y hki
        (not_lt.mp (Finset.mem_filter.mp hk).2)
      have hzbar := Mbar.gammaMap_single_apply_of_le z y hki
        (not_lt.mp (Finset.mem_filter.mp hk).2)
      simp [T, hz, hzbar, Pi.single_eq_of_ne hki]
  have hsplit : ∑ k, T k = ∑ k ∈ L, T k := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k => 𝒯.deg k < 𝒯.deg i)]
    change (∑ k ∈ L, T k) +
      ∑ k ∈ Finset.univ.filter (fun k => ¬𝒯.deg k < 𝒯.deg i), T k = _
    rw [hhigh, add_zero]
  have hlow :
      (∑ k ∈ L.filter (fun k => ¬𝒯.deg j < 𝒯.deg k), T k) =
        M.gammaMap y z (Pi.single i 1) j -
          Mbar.gammaMap y z (Pi.single i 1) j := by
    rw [Finset.sum_eq_single j]
    · have hji' : j ≠ i := by
        intro h
        subst h
        exact (lt_irrefl _ hji)
      simp [T, M.gammaMap_single_apply_self, Mbar.gammaMap_single_apply_self,
        Pi.single_eq_of_ne hji']
    · intro k hk hkj
      have hki : 𝒯.deg k < 𝒯.deg i :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
      have hkjdeg : 𝒯.deg k ≤ 𝒯.deg j := le_of_not_gt
        (Finset.mem_filter.mp hk).2
      have hki' : k ≠ i := by
        intro h
        subst k
        exact (lt_irrefl _ hki)
      have hz := M.gammaMap_single_apply_of_le y x (Ne.symm hkj) hkjdeg
      have hzbar := Mbar.gammaMap_single_apply_of_le y x (Ne.symm hkj) hkjdeg
      simp [T, hz, hzbar, Pi.single_eq_of_ne hki']
    · exact fun hj => (hj (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩, lt_irrefl _⟩)).elim
  have hlowB :
      (∑ k ∈ L, T k) =
        (∑ k ∈ L.filter (fun k => 𝒯.deg j < 𝒯.deg k), T k) +
          ∑ k ∈ L.filter (fun k => ¬𝒯.deg j < 𝒯.deg k), T k := by
    rw [← Finset.sum_filter_add_sum_filter_not L (fun k => 𝒯.deg j < 𝒯.deg k)]
  have hB :
      (∑ k ∈ L.filter (fun k => 𝒯.deg j < 𝒯.deg k), T k) =
        ∑ k ∈ B,
          ((M.gammaMap y z (Pi.single i 1) k -
              Mbar.gammaMap y z (Pi.single i 1) k) *
            M.gammaMap x y (Pi.single k 1) j +
          Mbar.gammaMap y z (Pi.single i 1) k *
            (M.gammaMap x y (Pi.single k 1) j -
              Mbar.gammaMap x y (Pi.single k 1) j)) := by
    apply Finset.sum_congr
    · ext k
      simp [B, L, and_comm]
    · intro k hk
      have hki : 𝒯.deg k < 𝒯.deg i := (Finset.mem_filter.mp hk).2.2
      have hki' : k ≠ i := by
        intro h
        subst k
        exact (lt_irrefl _ hki)
      simp [T, Pi.single_eq_of_ne hki']
  rw [M.gammaMap_single_diff_right_increment]
  change (∑ k, T k) = _
  rw [hsplit, hlowB, hB, hlow]
  ring

/- The two-model source estimate keeps one `C * ε^θ` factor in each product channel. -/

end RegularityStructures

end
