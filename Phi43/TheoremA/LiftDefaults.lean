/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.StepLifts

/-!
# Off-event defaults for lifted families

The measurable construction uses arbitrary values outside the full-measure growth event.  This
file supplies the zero-forcing model required for those values from the existence of the
renormalised canonical model.
-/

public section

namespace RegularityStructures.Phi43

private theorem assembly_zero_smooth : IsSmoothOnSpaceTime (fun _ : SpaceTime => 0) := by
  unfold IsSmoothOnSpaceTime
  exact contDiff_const

private theorem assembly_zero_growth : Statements.HasPhi43NoiseGrowth (fun _ : SpaceTime => 0) := by
  refine ⟨0, 0, fun k _ z => ?_⟩
  simp

theorem assembly_zero_model_of_canonicalModel
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
    (N : ℕ) (κ : Kappa) (C : RenormalisationConstants) :
    ∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
      Statements.IsModeratePhi43ModelOf N κ (fun _ : SpaceTime => 0) C Z := by
  exact assembly_model_exists_of_canonicalModel hG1 N κ (fun _ => 0) assembly_zero_smooth
    assembly_zero_growth C

end RegularityStructures.Phi43

end
