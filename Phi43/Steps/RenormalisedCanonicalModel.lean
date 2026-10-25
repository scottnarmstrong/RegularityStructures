/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsModerateRenormalisedCanonicalModel
public import Phi43.Structure.CanonicalPolynomialWeight
public import Phi43.Structure.CanonicalModelExistenceGrowth
public import Phi43.Structure.CanonicalWeightedUniqueness

/-!
# The renormalised canonical model of a smooth noise

For a smooth noise with polynomially growing derivatives and renormalisation constants `C`, the
renormalised canonical model exists with the properties of `IsModerateRenormalisedCanonicalModel`,
and is unique below the cutoff `γ` [Hai14, Proposition 8.27, (8.34), Theorem 5.14]. The theorem
`renormalisedCanonicalModel_existsUnique` has exactly the statement
`Statements.renormalisedCanonicalModel_existsUnique` of
`Phi43Statements.Steps.RenormalisedCanonicalModel`.

The uniqueness conjunct is assembled from the weighted `Π` and `Γ` halves in
`Phi43.Structure.CanonicalWeightedUniqueness`.
-/

public section

namespace RegularityStructures.Phi43

/-- Existence of the renormalised canonical model [Hai14, Proposition 8.27, (8.34)]. -/
theorem exists_isModerateRenormalisedCanonicalModel
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
      Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z := by
  obtain ⟨Z, hZ, B, hB, q', hPi⟩ :=
    canonicalRenormalisedModel_exists_with_piBoundGrowth N κ noise Cg q hg C
  refine ⟨Z, ?_⟩
  unfold Statements.IsModerateRenormalisedCanonicalModel
  refine ⟨hZ.1, hZ.2.1, hZ.2.2, ?_⟩
  exact ⟨fun z => (1 + parabolicNorm z) ^ q', q', B,
    canonicalPolynomialWeight_isModerate q', hB, hPi⟩

/-- **The renormalised canonical model** exists and is unique below the cutoff `γ`. -/
theorem renormalisedCanonicalModel_existsUnique
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    (∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
      Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z) ∧
    ∀ Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup,
      Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z →
      Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z' →
        Z.diffNormOn Z' (gamma κ) Set.univ = 0 := by
  refine ⟨exists_isModerateRenormalisedCanonicalModel N κ noise Cg q hg C, ?_⟩
  intro Z Z' hZ hZ'
  have hPi := renormalisedCanonicalModel_piDiffNormOn_eq_zero
    N κ noise C Z Z' hZ hZ'
  have hGamma := renormalisedCanonicalModel_gammaDiffNormOn_eq_zero
    N κ noise C Z Z' hZ hZ'
  simp [Model.diffNormOn, hPi, hGamma]

end RegularityStructures.Phi43

end
