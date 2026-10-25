/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.BoundedTauRelations

/-!
# Bounded-lifetime extension from an explicit continuation witness

The explicit witness form is useful in the explosion argument: the persistence interval is selected
first, then an active time is chosen sufficiently close to the lifetime endpoint.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyBoundedTau_gt_of_continuationWitness
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω)
    {s t₀ R L : ℝ} (hs : 0 ≤ s) (ht₀ : 0 < t₀)
    (hbefore : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) s,
      ‖x n ω t‖ ≤ L)
    (hafter : ∀ n : ℕ, ∀ t ∈ Icc s (s + t₀),
      ‖x n ω t‖ ≤ R) :
    ENNReal.ofReal (s + t₀ / 2) < assemblyBoundedTau x hcont ω := by
  let t₁ : ℝ := t₀ / 2
  have ht₁ : 0 < t₁ := by
    dsimp [t₁]
    linarith
  let M : ℝ := max L R
  have hbound : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (s + t₀),
      ‖x n ω t‖ ≤ M := by
    intro n t ht
    by_cases hts : t ≤ s
    · exact (hbefore n t ⟨ht.1, hts⟩).trans (le_max_left _ _)
    · exact (hafter n t ⟨le_of_not_ge hts, ht.2⟩).trans (le_max_right _ _)
  obtain ⟨q, hq₁, hq₀⟩ := exists_rat_btwn
    (show s + t₁ < s + t₀ by
      dsimp [t₁]
      linarith only [ht₀])
  obtain ⟨K, hK⟩ := exists_nat_ge M
  have hE : assemblyRationalBoundedPathEvent q K x hcont ω := by
    refine ⟨?_, ?_⟩
    have hst₁ : 0 < s + t₁ := by linarith only [hs, ht₁]
    exact_mod_cast (lt_trans hst₁ hq₁)
    intro n r hr
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
    have hrq : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hr.2
    exact (hbound n (r : ℝ) ⟨hr0, hrq.trans (le_of_lt hq₀)⟩).trans hK
  have hs₁ : 0 ≤ s + t₁ := by linarith only [hs, ht₁]
  apply (assemblyBoundedTau_lt_iff x hcont ω ⟨q, K, hE⟩ hs₁).2
  exact ⟨q, K, hq₁, hE⟩

end RegularityStructures.Phi43

end
