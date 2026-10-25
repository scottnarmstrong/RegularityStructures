/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.BphzCauchyTransfer
public import Phi43.BPHZ.RandomCanonical
import Mathlib.Tactic

/-!
# Replacing the given models by canonical ones

These are the first two steps of the Cauchy argument for the BPHZ models.

* `ae_hasPhi43NoiseGrowth_of_noiseCauchy`: the growth clause of the Cauchy property of the noises
  (`phi43Noise_cauchy`), for the regularised noise of one scale.
* `exists_canonical_replacement`: for a regularised noise `ξ` with almost surely moderate Φ⁴₃
  models `Z` (`Statements.IsModeratePhi43ModelOf`), there is a modification `ξ₁` of `ξ` such that
  for all `ω` the canonical model of `ξ₁ ω` is a moderate Φ⁴₃ model of `ξ₁ ω`, and almost surely
  `Z ω` and this canonical model have vanishing local difference norm on `S` (the uniqueness
  clause of `renormalisedCanonicalModel_existsUnique`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem ae_hasPhi43NoiseGrowth_of_noiseCauchy (hG7 : Phi43.NoiseCauchyStatement.{u})
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ : ℝ → Ω → SpaceTime → ℝ} (hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) : ∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ε ω) :=
  ((hG7 ⟨-1, by norm_num⟩ (by norm_num)).2.1 ρ hρ P W hW ξ hξ ε hε).2

theorem exists_canonical_replacement {N : ℕ} {κ : Kappa} (hG1 : Phi43.RenormalisedCanonicalModelStatement)
    (hcan : CanonicalLiftGrowth N κ) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hgr : ∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω))
    {C : RenormalisationConstants}
    {Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : ∀ᵐ ω ∂P, Statements.IsModeratePhi43ModelOf N κ (ξ ω) C (Z ω)) (S : Set ParabolicSpace) :
    ∃ ξ₁ : Ω → SpaceTime → ℝ, IsRegularisedNoise P W ρ ε ξ₁ ∧
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ₁ ω)) ∧
      ∀ᵐ ω ∂P, (Z ω).diffNormOn (canonicalModelOfLift N κ C (ξ₁ ω)) (gamma κ) S = 0 := by
  obtain ⟨ξ₁, G, hGm, hG0, hreg, heq, hsg, -, -⟩ := exists_canonical_modification N κ C hξ hgr
  refine ⟨ξ₁, hreg, fun ω => (hsg ω).2, ?_⟩
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]; exact hG0
  filter_upwards [hZ, hG, hgr] with ω hω hωG hgω
  have h1 : Statements.IsModeratePhi43ModelOf N κ (ξ₁ ω) C (canonicalModelOfLift N κ C (ξ₁ ω)) :=
    isModeratePhi43ModelOf_canonicalModelOfLift (hcan) (hsg ω).1 (hsg ω).2
  rw [heq ω hωG] at h1 ⊢
  exact diffNormOn_eq_zero_of_isModeratePhi43ModelOf hG1 hgω hω h1 S

end RegularityStructures.Phi43

end
