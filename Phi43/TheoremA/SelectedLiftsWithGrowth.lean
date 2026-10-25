/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.LiftDefaults
public import Phi43.Mollifier

/-!
# Pointwise lift selection on the growth event

The measurable selector used in the proof of Theorem A is arbitrary off the growth event.
This module records the pointwise implication on the growth event, which is needed by the
pointwise explosion clause of the limit predicate.
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem assembly_selected_lifts_with_growth
    {Ω : Type*} {N : ℕ} {κ : Kappa}
    (hG1 : ∀ (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
      (_hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
      (C : RenormalisationConstants),
      (∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
        Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z) ∧
      ∀ Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup,
        Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z →
        Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z' →
          Z.diffNormOn Z' (gamma κ) Set.univ = 0)
    {ξ : ℝ → Ω → SpaceTime → ℝ}
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1,
      ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    {C : ℝ → RenormalisationConstants}
    (hpotential : ∀ f : SpaceTime → ℝ, IsSmoothOnSpaceTime f →
      Statements.HasPhi43NoiseGrowth f →
      ∃ ψ : ℝ → C(Torus3, ℝ), RegularityStructures.IsMassivePotential f ψ) :
    ∃ (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
      (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)),
      ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω,
        Statements.HasPhi43NoiseGrowth (ξ ε ω) →
          Statements.IsModeratePhi43Lift N κ (ξ ε ω) (C ε) (Z ε ω) (ψ ε ω) := by
  classical
  let Z₀ : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup :=
    fun ε _ => Classical.choose (assembly_zero_model_of_canonicalModel hG1 N κ (C ε))
  let Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup :=
    fun ε ω => if h : ∃ z, Statements.IsModeratePhi43ModelOf N κ (ξ ε ω) (C ε) z then
      h.choose else Z₀ ε ω
  let ψ : ℝ → Ω → ℝ → C(Torus3, ℝ) :=
    fun ε ω => if h : ∃ p, RegularityStructures.IsMassivePotential (ξ ε ω) p then
      h.choose else 0
  refine ⟨Z, ψ, ?_⟩
  intro ε hε ω hg
  have hM : ∃ z, Statements.IsModeratePhi43ModelOf N κ (ξ ε ω) (C ε) z :=
    assembly_model_exists_of_canonicalModel hG1 N κ (ξ ε ω) (hξ ε hε ω) hg (C ε)
  have hP : ∃ p, RegularityStructures.IsMassivePotential (ξ ε ω) p :=
    hpotential (ξ ε ω) (hξ ε hε ω) hg
  have hMs : Statements.IsModeratePhi43ModelOf N κ (ξ ε ω) (C ε) (Z ε ω) := by
    simp [Z, hM]
    exact hM.choose_spec
  have hPs : RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω) := by
    simp [ψ, hP]
    exact hP.choose_spec
  exact ⟨hg, hMs, hPs⟩

end RegularityStructures.Phi43

end
