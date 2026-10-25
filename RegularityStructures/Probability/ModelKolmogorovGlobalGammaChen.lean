/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGlobalGammaIncrements
public import RegularityStructures.Abstract.QFamilyModelBound

/-!
# Strictly graded Chen increments of model coordinates

This is an ingredient of the Kolmogorov criterion for models [Hai14, Theorem 10.7]. Graded
unipotence reduces the full cocycle sum to its leading increment and strictly intermediate degrees.
Consequently only the source's strict-lower Gamma moments will be needed in the moment estimate.

Source: [Hai14, Definition 2.17, first algebraic condition], together with the triangularity of the
structure group.
-/

public section

open MeasureTheory

namespace RegularityStructures.Model

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {μ : Measure E} {𝒯 : RegularityStructure ι} {Q : RegularisingSemigroup E μ}

/-- The Chen increment has only strictly intermediate-degree product terms. -/
theorem gammaMap_single_left_increment_lower
    (M : Model 𝒯 Q) (x y z : E) {i j : ι} (hji : 𝒯.deg j < 𝒯.deg i) :
    M.gammaMap z x (Pi.single i 1) j - M.gammaMap y x (Pi.single i 1) j =
      M.gammaMap z y (Pi.single i 1) j +
        ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i),
          M.gammaMap y x (Pi.single i 1) k * M.gammaMap z y (Pi.single k 1) j := by
  classical
  let L := Finset.univ.filter (fun k => 𝒯.deg k < 𝒯.deg i)
  let B := Finset.univ.filter (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i)
  let T : ι → ℝ := fun k => M.gammaMap y x (Pi.single i 1) k *
    (M.gammaMap z y (Pi.single k 1) j - (Pi.single k 1 : ι → ℝ) j)
  have hne : j ≠ i := fun h => (ne_of_lt hji) (congrArg 𝒯.deg h)
  have htop : (∑ k ∈ Finset.univ.filter (fun k => ¬𝒯.deg k < 𝒯.deg i), T k) =
      M.gammaMap z y (Pi.single i 1) j := by
    rw [Finset.sum_eq_single i]
    · simp [T, M.gammaMap_single_apply_self, Pi.single_eq_of_ne hne]
    · intro k hk hki
      have hz := M.gammaMap_single_apply_of_le x y hki
        (not_lt.mp (Finset.mem_filter.mp hk).2)
      simp only [T, hz, zero_mul]
    · intro hi
      exact (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_irrefl _⟩)).elim
  have hBL : B ⊆ L := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.2⟩
  have hzero : ∀ k ∈ L, k ∉ B → T k = 0 := by
    intro k hk hkb
    have hki : 𝒯.deg k < 𝒯.deg i := (Finset.mem_filter.mp hk).2
    have hjk : 𝒯.deg k ≤ 𝒯.deg j := le_of_not_gt (fun h =>
      hkb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hki⟩))
    by_cases he : j = k
    · subst j
      simp [T, M.gammaMap_single_apply_self]
    · have hz := M.gammaMap_single_apply_of_le y z he hjk
      simp [T, hz, Pi.single_eq_of_ne he]
  have hlow : (∑ k ∈ L, T k) =
      ∑ k ∈ B, M.gammaMap y x (Pi.single i 1) k * M.gammaMap z y (Pi.single k 1) j := by
    rw [← Finset.sum_subset hBL hzero]
    apply Finset.sum_congr rfl
    intro k hk
    have hjk : j ≠ k := fun h =>
      (ne_of_lt (Finset.mem_filter.mp hk).2.1) (congrArg 𝒯.deg h)
    simp only [T, Pi.single_eq_of_ne hjk, sub_zero]
  rw [M.gammaMap_single_left_increment x y z i j]
  change (∑ k, T k) = _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun k => 𝒯.deg k < 𝒯.deg i), htop]
  change (∑ k ∈ L, T k) + _ = _
  rw [hlow]
  exact add_comm _ _

/-- The difference Chen identity retains both strictly intermediate error channels. -/
theorem gammaMap_single_diff_left_increment_lower
    (M Mbar : Model 𝒯 Q) (x y z : E) {i j : ι} (hji : 𝒯.deg j < 𝒯.deg i) :
    (M.gammaMap z x (Pi.single i 1) j - Mbar.gammaMap z x (Pi.single i 1) j) -
      (M.gammaMap y x (Pi.single i 1) j - Mbar.gammaMap y x (Pi.single i 1) j) =
      (M.gammaMap z y (Pi.single i 1) j - Mbar.gammaMap z y (Pi.single i 1) j) +
        ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i),
          ((M.gammaMap y x (Pi.single i 1) k - Mbar.gammaMap y x (Pi.single i 1) k) *
            M.gammaMap z y (Pi.single k 1) j +
          Mbar.gammaMap y x (Pi.single i 1) k *
            (M.gammaMap z y (Pi.single k 1) j - Mbar.gammaMap z y (Pi.single k 1) j)) := by
  have he : (∑ k ∈ Finset.univ.filter
      (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i),
        ((M.gammaMap y x (Pi.single i 1) k - Mbar.gammaMap y x (Pi.single i 1) k) *
          M.gammaMap z y (Pi.single k 1) j +
        Mbar.gammaMap y x (Pi.single i 1) k *
          (M.gammaMap z y (Pi.single k 1) j - Mbar.gammaMap z y (Pi.single k 1) j))) =
      (∑ k ∈ Finset.univ.filter
        (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i),
          M.gammaMap y x (Pi.single i 1) k * M.gammaMap z y (Pi.single k 1) j) -
      ∑ k ∈ Finset.univ.filter
        (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i),
          Mbar.gammaMap y x (Pi.single i 1) k * Mbar.gammaMap z y (Pi.single k 1) j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  linarith [M.gammaMap_single_left_increment_lower x y z hji,
    Mbar.gammaMap_single_left_increment_lower x y z hji]

end RegularityStructures.Model

end

