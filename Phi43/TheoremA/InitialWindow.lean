/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43.ClassicalSolution
public import RegularityStructures.Torus.HolderBesov

/-!
# The first uniform window

Persistence of classical solutions gives one common time interval on which a family of smooth
classical solutions is bounded, provided its lifted sizes have one common bound.  This is the local
step used to show that the explosion-level construction has positive lifetime.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assembly_initial_window_of_steps
    {κ : Kappa} {N : ℕ} {η : NegExponent}
    (hPersistence : ∀ L B : ℝ, 1 ≤ L → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
        (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ))
        (u : ℝ → C(Torus3, ℝ)) (T : ℝ),
        Statements.IsModeratePhi43Lift N κ f C Z ψ →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        1 ≤ T → Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ s ∈ Icc (0 : ℝ) T, holderBesovENorm η (u s) ≤ ENNReal.ofReal L →
          ∀ t ∈ Icc s (s + t₀), holderBesovENorm η (u t) ≤ ENNReal.ofReal R)
    {L B : ℝ} (hL : 1 ≤ L) (hB : 1 ≤ B)
    {u₀ : C(Torus3, ℝ)} {f : ℕ → SpaceTime → ℝ}
    {C : ℕ → RenormalisationConstants}
    {Z : ℕ → Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ : ℕ → ℝ → C(Torus3, ℝ)} {u : ℕ → ℝ → C(Torus3, ℝ)}
    (hLift : ∀ n, Statements.IsModeratePhi43Lift N κ (f n) (C n) (Z n) (ψ n))
    (hclass : ∀ n, IsClassicalSolution (3 * (C n).1 - 9 * (C n).2)
      (f n) u₀ (u n))
    (hsize : ∀ n, Statements.phi43Size κ η 1 (Z n) (ψ n) ≤ ENNReal.ofReal B)
    (hinitial : ∀ n, u n 0 = u₀)
    (hinitial_bound : holderBesovENorm η u₀ ≤ ENNReal.ofReal L) :
    ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ n, ∀ t ∈ Icc (0 : ℝ) t₀,
        holderBesovENorm η (u n t) ≤ ENNReal.ofReal R := by
  obtain ⟨t₀, R, ht₀, ht₀1, hR⟩ := hPersistence L B hL hB
  refine ⟨t₀, R, ht₀, ht₀1, ?_⟩
  intro n t ht
  have hinitial_bound_n : holderBesovENorm η (u n 0) ≤ ENNReal.ofReal L := by
    rw [hinitial n]
    exact hinitial_bound
  have h := hR (f n) (C n) (Z n) (ψ n) u₀ (u n) 1
    (hLift n) (hclass n) le_rfl (hsize n) 0 ⟨le_rfl, zero_le_one⟩ hinitial_bound_n
  have ht' : t ∈ Icc (0 : ℝ) (0 + t₀) := by simpa only [zero_add] using ht
  simpa only [zero_add] using h t ht'

end RegularityStructures.Phi43

end
