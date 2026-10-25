/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.Measurable
public import Phi43.ClassicalSolution.PathContinuity
public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.Structure.Renormalisation
public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# Measurable continuous dyadic paths

For the dyadic classical solutions used in the proof of Theorem A, the first half of item (W5) of
Lemma 4.1 of the statement gives continuity in the completed Holder--Besov space, and the second
half gives measurability at each fixed time.  The coefficient is written in the shifted form
`a + 3 C₁^ε - 9 C₂^ε` used in the proof.
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

open RegularityStructures

theorem assembly_dyadic_holder_paths_of_steps
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {η : NegExponent} {ξ : ℝ → Ω → SpaceTime → ℝ}
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    {u₀ : C(Torus3, ℝ)} (hu₀ : IsSmoothOnTorus u₀)
    {C : ℝ → RenormalisationConstants}
    {u : ℕ → Ω → ℝ → C(Torus3, ℝ)}
    (hclass : ∀ n ω, IsClassicalSolution
      (3 * (C ((2 : ℝ) ^ n)⁻¹).1 - 9 * (C ((2 : ℝ) ^ n)⁻¹).2)
      (ξ ((2 : ℝ) ^ n)⁻¹ ω) u₀ (u n ω)) :
    (∀ n ω, ContinuousOn (fun t => toHolderBesov η (u n ω t)) (Ici (0 : ℝ))) ∧
    (∀ n t, 0 ≤ t → Measurable (fun ω => toHolderBesov η (u n ω t))) := by
  constructor
  · intro n ω
    exact classicalSolution_continuousOn η (hclass n ω)
  · intro n t ht
    have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hε : ((2 : ℝ) ^ n)⁻¹ ∈ Ioc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact inv_le_one_of_one_le₀ hpow
    exact classicalSolution_measurable η P W hW ρ hρ hε (ξ ((2 : ℝ) ^ n)⁻¹)
      (hξ ((2 : ℝ) ^ n)⁻¹ hε)
      (3 * (C ((2 : ℝ) ^ n)⁻¹).1 - 9 * (C ((2 : ℝ) ^ n)⁻¹).2) u₀ hu₀
      (u n) (hclass n) ht

end RegularityStructures.Phi43

end
