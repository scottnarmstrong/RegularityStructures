/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalModelExistence
public import Phi43.Structure.RenormalisedGrowthWeightedBounds
public import RegularityStructures.Abstract.Model

/-!
# Weighted existence for the renormalised canonical model

The explicit corrected smooth model satisfies the renormalised-model
predicate and, independently, has a polynomially weighted `PiBoundGrowth`.
The weight is derived from the polynomial growth hypothesis on the noise; no
analytic bound on the model is an input. This is the existence part of the
canonical and renormalised models [Hai14, Proposition 8.27, Theorem 8.44]
with polynomial weights; weighted uniqueness is proved separately.
-/

public section

namespace RegularityStructures.Phi43

theorem canonicalRenormalisedModel_exists_with_piBoundGrowth
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
      Statements.IsRenormalisedCanonicalModel N κ noise C Z ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∃ q' : ℕ,
        Z.PiBoundGrowth (gamma κ) B (fun z => (1 + parabolicNorm z) ^ q') := by
  refine ⟨canonicalRenormalisedModel N κ noise Cg q hg C,
    canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C,
    ?_⟩
  exact canonicalRenormalisedModel_piBoundGrowth N κ noise Cg q hg C

end RegularityStructures.Phi43

end
