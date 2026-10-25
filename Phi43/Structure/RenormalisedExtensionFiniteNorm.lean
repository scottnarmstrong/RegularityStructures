/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionPiBounds
public import Phi43.Structure.RenormalisedGammaBounds
public import RegularityStructures.Abstract.Model

/-!
# Finite compact norms of the actual renormalised smooth Model

The already derived Pi and Gamma estimates give the finite-norm clause
of the canonical-model predicate `Statements.IsRenormalisedCanonicalModel`,
without assuming any model bound [Hai14, Theorem 8.44].
-/

public noncomputable section

open scoped NNReal ENNReal

namespace RegularityStructures.Phi43

/-- The genuine corrected smooth Model has finite norms on every compact set. -/
theorem canonicalRenormalisedModel_normOn_ne_top (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) (hS : IsCompact S) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).normOn (gamma κ) S ≠ ⊤ := by
  obtain ⟨A, hA0, hA⟩ := canonicalRenormalisedModel_pi_bounds N κ noise Cg q hg C hS
  obtain ⟨B, hB0, hB⟩ := canonicalRenormalisedModel_gamma_bounds N κ noise Cg q hg C hS
  let M := canonicalRenormalisedModel N κ noise Cg q hg C
  let a : NNReal := ⟨A, hA0⟩
  let b : NNReal := ⟨B, hB0⟩
  have hp : M.piNormOn (gamma κ) S ≤ (a : ENNReal) :=
    (Model.piNormOn_le_iff M a).2 hA
  have hg' : M.gammaNormOn (gamma κ) S ≤ (b : ENNReal) :=
    (Model.gammaNormOn_le_iff M b).2 hB
  have hn : M.normOn (gamma κ) S ≤ (a : ENNReal) + (b : ENNReal) := add_le_add hp hg'
  exact ne_top_of_le_ne_top (by simp) hn

end RegularityStructures.Phi43

end
