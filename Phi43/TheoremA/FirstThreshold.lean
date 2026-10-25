/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Order.Compact

/-!
# First-threshold extraction for stopped comparisons

The stopped-continuity argument compares two paths only while both remain below a
fixed level.  This elementary compactness lemma supplies the first level-hitting
time needed for the usual exit contradiction.
-/

public section

open Set

namespace RegularityStructures.Phi43

theorem assembly_exists_first_threshold
    {T L : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (h0 : f 0 < L)
    (hbad : ∃ t ∈ Icc (0 : ℝ) T, L ≤ f t) :
    ∃ s ∈ Icc (0 : ℝ) T, f s = L ∧
      ∀ r ∈ Icc (0 : ℝ) s, f r ≤ L := by
  let S : Set ℝ := Icc (0 : ℝ) T ∩ f ⁻¹' Ici L
  have hSclosed : IsClosed S := by
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, hft⟩ := hbad
    exact ⟨t, ht, hft⟩
  obtain ⟨s, hs⟩ := hScompact.exists_isLeast hSne
  have hs_mem : s ∈ S := hs.1
  have hsIcc : s ∈ Icc (0 : ℝ) T := (show s ∈ Icc (0 : ℝ) T ∩ f ⁻¹' Ici L from hs_mem).1
  have hsfge : L ≤ f s := (show s ∈ Icc (0 : ℝ) T ∩ f ⁻¹' Ici L from hs_mem).2
  have hspos : 0 < s := by
    have hsz : s ≠ 0 := by
      intro hsz
      have : L ≤ f 0 := by simpa [hsz] using hsfge
      exact (not_le_of_gt h0) this
    exact lt_of_le_of_ne hsIcc.1 (Ne.symm hsz)
  have hsle : f s ≤ L := by
    by_contra hnot
    have hfs : L < f s := lt_of_not_ge hnot
    have hcont := hf s hsIcc
    obtain ⟨δ, hδ, hδf⟩ :=
      (Metric.continuousWithinAt_iff.1 hcont) (f s - L) (sub_pos.mpr hfs)
    let d : ℝ := min (s / 2) (δ / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (div_pos hspos (by norm_num)) (div_pos hδ (by norm_num))
    let r : ℝ := s - d
    have hr0 : 0 ≤ r := by
      dsimp [r]
      linarith [min_le_left (s / 2) (δ / 2)]
    have hrs : r ≤ T := by
      dsimp [r]
      linarith [hsIcc.2]
    have hrd : dist r s < δ := by
      rw [Real.dist_eq]
      dsimp [r]
      have hneg : s - d - s ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      have hdδ : d < δ := by
        exact (min_le_right (s / 2) (δ / 2)).trans_lt (by linarith [hδ])
      linarith
    have hrf : L < f r := by
      have hclose := hδf ⟨hr0, hrs⟩ hrd
      rw [Real.dist_eq] at hclose
      have hclose' : f s - f r < f s - L := by
        linarith [(abs_lt.mp hclose).1]
      linarith
    have hSle : s ≤ r := hs.2 ⟨⟨hr0, hrs⟩, hrf.le⟩
    dsimp [r] at hSle
    linarith
  have hsval : f s = L := le_antisymm hsle hsfge
  refine ⟨s, hsIcc, hsval, ?_⟩
  intro r hr
  by_contra hnot
  have hfrge : L ≤ f r := le_of_not_ge hnot
  have hSr : r ∈ S := ⟨⟨hr.1, hr.2.trans hsIcc.2⟩, hfrge⟩
  have hsr : s ≤ r := hs.2 hSr
  have hfr : L < f r := lt_of_not_ge hnot
  have hrs_eq : r = s := le_antisymm hr.2 hsr
  rw [hrs_eq, hsval] at hfr
  exact (lt_irrefl L) hfr

end RegularityStructures.Phi43

end
