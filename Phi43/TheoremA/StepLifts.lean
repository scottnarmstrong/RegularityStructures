/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.IsModerateRenormalisedCanonicalModel
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import RegularityStructures.Statements.Defs.IsMassivePotential
public import Phi43.BPHZ.CanonicalBridgeData
public import RegularityStructures.Probability.ModelKolmogorovNorm

/-!
# Lifts from the canonical model and the massive potential

These lemmas unpack the existence and uniqueness of the renormalised canonical model and the
deterministic massive-potential part of the convergence of the noise potentials. The periodic
canonical noise is `canonicalNoiseOfSpaceTime`.
-/

public section

open Set

namespace RegularityStructures.Phi43

theorem assembly_model_exists_of_canonicalModel
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
    (N : ℕ) (κ : Kappa) (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (C : RenormalisationConstants) :
    ∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
      Statements.IsModeratePhi43ModelOf N κ f C Z := by
  obtain ⟨Cg, q, hgq⟩ := hg
  let noise : CanonicalNoise := canonicalNoiseOfSpaceTime f hf
  obtain ⟨⟨Z, hZ⟩, -⟩ := hG1 N κ noise Cg q (by
    intro k hk z
    simpa [noise, canonicalNoiseOfSpaceTime, spaceTimeProj] using hgq k hk z) C
  refine ⟨Z, noise, ?_, hZ⟩
  intro z
  rfl

end RegularityStructures.Phi43

end
