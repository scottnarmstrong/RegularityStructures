/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.EventualContinuation
public import Phi43.TheoremA.StoppedLimitWindowBound
public import Phi43.TheoremA.BoundedTau
public import Phi43.ClassicalSolution
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size

/-!
# Explosion from persistence

This is the contradiction argument for condition (A2) of Theorem A, in the bounded-lifetime
presentation.  A bound on the stopped
limit selects one persistence witness first; a time close to a finite lifetime is then chosen, and
the eventual-to-all-index bridge supplies a larger bounded rational interval.
-/

public section

open Filter Topology Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assembly_explosion_of_persistence_eventual
    {Ω : Type*} {η : NegExponent} {κ : Kappa} {N : ℕ}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (u : ℕ → Ω → ℝ → C(Torus3, ℝ))
    (hident : ∀ n ω t, x n ω t = toHolderBesov η (u n ω t))
    (τ : Ω → ℝ≥0∞)
    (hCauchy : ∀ ω t, 0 ≤ t → ENNReal.ofReal t < τ ω →
      CauchySeq (fun n => x n ω t))
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hwindow : ∀ ω T, 0 ≤ T → ENNReal.ofReal T < τ ω →
      CauchySeq (fun n =>
        ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n ω t.1)
          (continuousOn_iff_continuous_domRestrict.mp
            ((hcont n ω).mono Icc_subset_Ici_self))))
    {ω : Ω} (hτeq : assemblyBoundedTau x hcont ω = τ ω)
    (hτpos : 0 < τ ω)
    (hPersistence : ∀ A B : ℝ, 1 ≤ A → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧
      ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
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
    {B T : ℝ} (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hτT : (τ ω).toReal ≤ T)
    {u₀ : C(Torus3, ℝ)} {f : ℕ → SpaceTime → ℝ}
    {C : ℕ → RenormalisationConstants}
    {Z : ℕ → Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ : ℕ → ℝ → C(Torus3, ℝ)}
    (hLift : ∀ n, Statements.IsModeratePhi43Lift N κ (f n) (C n) (Z n) (ψ n))
    (hclass : ∀ n, IsClassicalSolution (3 * (C n).1 - 9 * (C n).2)
      (f n) u₀ (u n ω))
    (hsize : ∀ n, Statements.phi43Size κ η T (Z n) (ψ n) ≤ ENNReal.ofReal B)
    (hbounded : BddAbove ((fun t => ‖assemblyStoppedLimit x τ hCauchy ω t‖) ''
      {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω})) :
    τ ω < ⊤ → False := by
  intro hfinite
  obtain ⟨L, hL⟩ := hbounded
  have hv : ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω →
      ‖assemblyStoppedLimit x τ hCauchy ω t‖ ≤ L := by
    intro t ht htτ
    exact hL ⟨t, ⟨ht, htτ⟩, rfl⟩
  let A : ℝ := max (L + 2) 1
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_max_right _ _
  have hLA : L + 1 ≤ A := by
    dsimp [A]
    exact (by linarith : L + 1 ≤ L + 2).trans (le_max_left _ _)
  obtain ⟨t₀, R, ht₀, hR⟩ := hPersistence A B hA hB
  have hrealpos : 0 < (τ ω).toReal :=
    ENNReal.toReal_pos hτpos.ne' hfinite.ne
  have hlow : max 0 ((τ ω).toReal - t₀ / 2) < (τ ω).toReal := by
    apply max_lt_iff.mpr
    constructor
    · exact hrealpos
    · linarith
  obtain ⟨s, hslow, hshi⟩ := exists_between hlow
  have hs : 0 ≤ s := by
    exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hslow)
  have hsτ : ENNReal.ofReal s < τ ω :=
    (ENNReal.ofReal_lt_iff_lt_toReal hs hfinite.ne).mpr hshi
  have hsT : s ≤ T := by
    exact (le_of_lt hshi).trans hτT
  let y : C(Icc (0 : ℝ) s, HolderBesov η) :=
    assembly_path_limit (fun n => x n ω) (fun n => hcont n ω)
      (hwindow ω s hs hsτ)
  have hlim : Tendsto (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) s => x n ω t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n ω).mono Icc_subset_Ici_self))) atTop (𝓝 y) := by
    simpa only [y] using assembly_path_limit_spec
      (fun n => x n ω) (fun n => hcont n ω) (hwindow ω s hs hsτ)
  have hy : ∀ t : Icc (0 : ℝ) s, ‖y t‖ ≤ L := by
    simpa only [y] using
      (assemblyStoppedLimit_windowLimit_bound x τ hCauchy hcont hwindow hs hsτ
        (fun t ht => hv t ht.1 ((ENNReal.ofReal_mono ht.2).trans_lt hsτ)))
  have hext := assemblyBoundedTau_gt_of_eventualStoppedWitness x u hident hcont ω hs
    hT hsT hLA ht₀ y hlim hy hR hLift hclass hsize
  rw [hτeq] at hext
  have hsplus : 0 ≤ s + t₀ / 2 := by linarith
  have hext' : s + t₀ / 2 < (τ ω).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hsplus hfinite.ne).mp hext
  have hslow' : (τ ω).toReal - t₀ / 2 < s := by
    exact lt_of_le_of_lt (le_max_right _ _) hslow
  linarith

end RegularityStructures.Phi43

end
