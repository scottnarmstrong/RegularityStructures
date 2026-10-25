/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.PathWindowPointwiseCauchy
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Order.CompletePartialOrder
public import Phi43.TheoremA.MaximalPathData

/-!
# Compact-window consequences of the maximal path events

The maximal-path event contains uniform Cauchy convergence on one rational window.  This
module extracts the corresponding window Cauchy property whenever the lifetime is active.
The explicit nonempty-event premise is needed because the historical definition assigns the
value `⊤` when no bounded event exists; the smooth assembly totalises that case separately.
-/

public section

open Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyTau_lt_iff_of_exists
    {Ω : Type*} {η : NegExponent} (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω)
    (hExists : ∃ q : ℚ, ∃ L : ℕ, assemblyPathEvent q L x hcont ω)
    {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t < assemblyTau x hcont ω ↔
      ∃ q : ℚ, ∃ L : ℕ, t < (q : ℝ) ∧
        assemblyPathEvent q L x hcont ω := by
  classical
  rw [assemblyTau_eq]
  simp only [hExists, ↓reduceIte]
  constructor
  · intro hτ
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp hτ
    obtain ⟨L, hqL⟩ := lt_iSup_iff.mp hq
    by_cases hE : assemblyPathEvent q L x hcont ω
    · have hqL' : ENNReal.ofReal t < ENNReal.ofReal (q : ℝ) := by
        simpa [hE] using hqL
      have hqpos : 0 < (q : ℝ) := by
        apply (ENNReal.ofReal_pos).mp
        exact lt_of_le_of_lt bot_le hqL'
      have hqt : t < (q : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff hqpos).mp hqL'
      exact ⟨q, L, hqt, hE⟩
    · simp [hE] at hqL
  · rintro ⟨q, L, hqt, hE⟩
    have hlt : ENNReal.ofReal t < ENNReal.ofReal (q : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr hqt
    exact hlt.trans_le (le_iSup_of_le q (le_iSup_of_le L (by simp [hE])))

theorem assemblyTau_window
    {Ω : Type*} {η : NegExponent} (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω)
    (hExists : ∃ q : ℚ, ∃ L : ℕ, assemblyPathEvent q L x hcont ω)
    {T : ℝ} (hT : 0 ≤ T) (hτ : ENNReal.ofReal T < assemblyTau x hcont ω) :
    CauchySeq (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n ω t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n ω).mono Icc_subset_Ici_self))) := by
  obtain ⟨q, L, hTq, hA⟩ :=
    (assemblyTau_lt_iff_of_exists x hcont ω hExists hT).mp hτ
  have hbig := assemblyPathEvent_cauchy q L x hcont ω hA
  rw [Metric.cauchySeq_iff'] at hbig ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := hbig (ε / 2) hhalf
  refine ⟨N, fun n hn => ?_⟩
  let _ : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  refine lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε)
  apply (ContinuousMap.dist_le_iff_of_nonempty (C := ε / 2)).mpr
  intro t
  have hbig_nm := hN n hn
  have hpoint := (ContinuousMap.dist_le (C := ε / 2) (by linarith)).mp
    (le_of_lt hbig_nm)
    (⟨t.1, t.2.1, t.2.2.trans (le_of_lt hTq)⟩ : Icc (0 : ℝ) (q : ℝ))
  change dist (x n ω t.1) (x N ω t.1) ≤ ε / 2
  rw [assemblyPathRestriction_eval, assemblyPathRestriction_eval] at hpoint
  exact hpoint

end RegularityStructures.Phi43

end
