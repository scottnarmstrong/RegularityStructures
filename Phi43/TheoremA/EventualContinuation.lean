/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.UniformNormLimit
public import Phi43.TheoremA.FiniteContinuousMapUniformBound
public import Phi43.TheoremA.BoundedTauWitnessExtension
public import Phi43.ClassicalSolution
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size

/-!
# Eventual-to-all-index continuation

The compact-window limit controls all sufficiently late approximants.  The finitely many early
approximants are bounded separately by compactness, allowing the bounded-lifetime event to use its
all-index formulation.
-/

public section

open Filter Topology Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyBoundedTau_gt_of_eventualStoppedWitness
    {Ω : Type*} {η : NegExponent} {κ : Kappa} {N : ℕ}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (u : ℕ → Ω → ℝ → C(Torus3, ℝ))
    (hident : ∀ n ω t, x n ω t = toHolderBesov η (u n ω t))
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω)
    {s T L A t₀ R : ℝ} (hs : 0 ≤ s) (hT : 1 ≤ T) (hsT : s ≤ T)
    (hLA : L + 1 ≤ A) (ht₀ : 0 < t₀)
    (y : C(Icc (0 : ℝ) s, HolderBesov η))
    (hlim : Tendsto (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) s => x n ω t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n ω).mono Icc_subset_Ici_self))) atTop (𝓝 y))
    (hy : ∀ t : Icc (0 : ℝ) s, ‖y t‖ ≤ L)
    {B : ℝ}
    (hPersistence : ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
      (ψ : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ))
      (u' : ℝ → C(Torus3, ℝ)) (T : ℝ),
      Statements.IsModeratePhi43Lift N κ f C Z ψ →
      IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u' →
      1 ≤ T → Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
      ∀ s ∈ Icc (0 : ℝ) T,
        holderBesovENorm η (u' s) ≤ ENNReal.ofReal A →
        ∀ t ∈ Icc s (s + t₀),
          holderBesovENorm η (u' t) ≤ ENNReal.ofReal R)
    {u₀ : C(Torus3, ℝ)} {f : ℕ → SpaceTime → ℝ}
    {C : ℕ → RenormalisationConstants}
    {Z : ℕ → Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ : ℕ → ℝ → C(Torus3, ℝ)}
    (hLift : ∀ n, Statements.IsModeratePhi43Lift N κ (f n) (C n) (Z n) (ψ n))
    (hclass : ∀ n, IsClassicalSolution (3 * (C n).1 - 9 * (C n).2)
      (f n) u₀ (u n ω))
    (hsize : ∀ n, Statements.phi43Size κ η T (Z n) (ψ n) ≤ ENNReal.ofReal B) :
    ENNReal.ofReal (s + t₀ / 2) < assemblyBoundedTau x hcont ω := by
  let xShort : ℕ → C(Icc (0 : ℝ) s, HolderBesov η) := fun n =>
    ContinuousMap.mk (fun t : Icc (0 : ℝ) s => x n ω t.1)
      (continuousOn_iff_continuous_domRestrict.mp
        ((hcont n ω).mono Icc_subset_Ici_self))
  obtain ⟨n₀, hn₀⟩ := assembly_eventual_uniformNorm_le_of_continuousMap_tendsto
    xShort y hlim hy
  let xLong : ℕ → C(Icc (0 : ℝ) (s + t₀), HolderBesov η) := fun n =>
    ContinuousMap.mk (fun t : Icc (0 : ℝ) (s + t₀) => x n ω t.1)
      (continuousOn_iff_continuous_domRestrict.mp
        ((hcont n ω).mono Icc_subset_Ici_self))
  obtain ⟨E, hE⟩ := assembly_finiteContinuousMap_uniformNorm_bound xLong n₀
  let R' : ℝ := max R 1
  have hR'0 : 0 ≤ R' := by
    dsimp [R']
    exact zero_le_one.trans (le_max_right _ _)
  have hlateHolder : ∀ n ≥ n₀,
      holderBesovENorm η (u n ω s) ≤ ENNReal.ofReal A := by
    intro n hn
    have hnorm : ‖x n ω s‖ ≤ L + 1 := by
      exact hn₀ n hn ⟨s, hs, le_rfl⟩
    have hreal : (holderBesovENorm η (u n ω s)).toReal ≤ L + 1 := by
      rw [← norm_toHolderBesov, ← hident n ω s]
      exact hnorm
    have htop : holderBesovENorm η (u n ω s) < ⊤ :=
      holderBesovENorm_lt_top η.2.le (u n ω s)
    calc
      holderBesovENorm η (u n ω s) =
          ENNReal.ofReal (holderBesovENorm η (u n ω s)).toReal :=
        (ENNReal.ofReal_toReal htop.ne).symm
      _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal hLA
  have hfull : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (s + t₀),
      ‖x n ω t‖ ≤ max E (max (L + 1) R') := by
    intro n t ht
    by_cases hn : n < n₀
    · exact (hE n hn ⟨t, ht⟩).trans (le_max_left _ _)
    · have hn' : n₀ ≤ n := le_of_not_gt hn
      by_cases hts : t ≤ s
      · have hlate : ‖x n ω t‖ ≤ L + 1 := by
          exact hn₀ n hn' ⟨t, ht.1, hts⟩
        exact hlate.trans ((le_max_left _ _).trans (le_max_right _ _))
      · have hst : s ≤ t := le_of_not_ge hts
        have hholder : holderBesovENorm η (u n ω t) ≤ ENNReal.ofReal R' := by
          have h := hPersistence (f n) (C n) (Z n) (ψ n) u₀ (u n ω) T
            (hLift n) (hclass n) hT (hsize n) s ⟨hs, hsT⟩
            (hlateHolder n hn') t ⟨hst, ht.2⟩
          exact h.trans (ENNReal.ofReal_mono (le_max_left _ _))
        have hnorm : ‖x n ω t‖ ≤ R' := by
          rw [hident n ω t, norm_toHolderBesov]
          exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hholder).trans_eq
            (ENNReal.toReal_ofReal hR'0)
        exact hnorm.trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbefore : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) s,
      ‖x n ω t‖ ≤ max E (max (L + 1) R') := by
    intro n t ht
    exact hfull n t ⟨ht.1, ht.2.trans (le_add_of_nonneg_right (le_of_lt ht₀))⟩
  have hafter : ∀ n : ℕ, ∀ t ∈ Icc s (s + t₀),
      ‖x n ω t‖ ≤ max E (max (L + 1) R') := by
    intro n t ht
    exact hfull n t ⟨le_trans hs ht.1, ht.2⟩
  exact assemblyBoundedTau_gt_of_continuationWitness x hcont ω hs ht₀
    hbefore hafter

end RegularityStructures.Phi43

end
