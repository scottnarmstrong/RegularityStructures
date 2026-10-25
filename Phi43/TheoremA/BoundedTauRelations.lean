/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.BoundedTau

/-!
# Rational characterization of the lifetime

On a path for which some rational interval is uniformly bounded, the definition of
`assemblyBoundedTau` is equivalent to the existence of a larger rational bounded interval.
This is the order-theoretic interface used by the stopped-path construction.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyBoundedTau_lt_iff
    {Ω : Type*} {η : NegExponent} (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω)
    (hExists : ∃ q : ℚ, ∃ L : ℕ,
      assemblyRationalBoundedPathEvent q L x hcont ω)
    {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t < assemblyBoundedTau x hcont ω ↔
      ∃ q : ℚ, ∃ L : ℕ, t < (q : ℝ) ∧
        assemblyRationalBoundedPathEvent q L x hcont ω := by
  classical
  rw [show assemblyBoundedTau x hcont ω =
      ⨆ q : ℚ, ⨆ L : ℕ,
        if assemblyRationalBoundedPathEvent q L x hcont ω then
          ENNReal.ofReal (q : ℝ) else 0 by
    simp [assemblyBoundedTau, hExists]]
  constructor
  · intro hτ
    obtain ⟨q, hq⟩ := (lt_iSup_iff.mp hτ)
    obtain ⟨L, hqL⟩ := (lt_iSup_iff.mp hq)
    by_cases hE : assemblyRationalBoundedPathEvent q L x hcont ω
    · have hqL' : ENNReal.ofReal t < ENNReal.ofReal (q : ℝ) := by
        simpa [hE] using hqL
      have hqt : t < (q : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff hE.1).mp hqL'
      exact ⟨q, L, hqt, hE⟩
    · simp [hE] at hqL
  · rintro ⟨q, L, hqt, hE⟩
    have hlt : ENNReal.ofReal t < ENNReal.ofReal (q : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr hqt
    exact hlt.trans_le (le_iSup_of_le q (le_iSup_of_le L (by simp [hE])))

theorem assemblyBoundedTau_event_of_uniformBound
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω)
    {t₀ L : ℝ} (ht₀ : 0 < t₀)
    (hbound : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) t₀,
      ‖x n ω t‖ ≤ L) :
    ∃ q : ℚ, ∃ K : ℕ,
      assemblyRationalBoundedPathEvent q K x hcont ω := by
  let _ := hcont
  obtain ⟨K, hK⟩ := exists_nat_ge L
  obtain ⟨q, hq0, hqt₀⟩ := exists_rat_btwn ht₀
  refine ⟨q, K, hq0, ?_⟩
  intro n r hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
  have hrq : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hr.2
  exact (hbound n (r : ℝ) ⟨hr0, hrq.trans (le_of_lt hqt₀)⟩).trans hK

end RegularityStructures.Phi43

end
