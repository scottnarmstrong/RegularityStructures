/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedGrowthWeightedBounds
public import Phi43.Structure.CanonicalPolynomialWeight
public import Phi43.BPHZ.BphzCauchyTransfer

/-!
# The weighted growth of the canonical lift (discharging `CanonicalLiftGrowth`)

On a smooth noise with polynomial growth of its derivatives of order `≤ 4`, the canonical lift
`canonicalModelOfLift N κ C f` is the canonical renormalised model, whose diagonal satisfies the
weighted bound `PiBoundGrowth` with the moderate weight `(1 + ‖z‖_𝔰)^q'`
(`canonicalRenormalisedModel_piBoundGrowth`, `canonicalPolynomialWeight_isModerate`). This is the
weighted growth clause of `IsModerateRenormalisedCanonicalModel`, so the hypothesis `hcan` of
`exists_canonical_replacement` holds; `bphzModels_cauchy_shifted` uses it in this form.
-/

public section

namespace RegularityStructures.Phi43

universe u

theorem canonicalLiftGrowth_holds (N : ℕ) (κ : Kappa) : CanonicalLiftGrowth N κ := by
  intro C f hf hg
  have h : IsSmoothOnSpaceTime f ∧ Statements.HasPhi43NoiseGrowth f := ⟨hf, hg⟩
  obtain ⟨B, hB, q', hb⟩ := canonicalRenormalisedModel_piBoundGrowth N κ
    (canonicalNoiseOfSpaceTime f h.1) (Classical.choose h.2)
    (Classical.choose (Classical.choose_spec h.2))
    (Classical.choose_spec (Classical.choose_spec h.2)) C
  refine ⟨fun z => (1 + parabolicNorm z) ^ q', q', B,
    canonicalPolynomialWeight_isModerate q', hB, ?_⟩
  unfold canonicalModelOfLift
  simp only [h, and_self, ↓reduceDIte]
  exact hb

end RegularityStructures.Phi43

end
