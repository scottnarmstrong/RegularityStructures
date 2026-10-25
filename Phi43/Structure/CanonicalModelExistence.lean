/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsRenormalisedCanonicalModel
public import Phi43.Structure.RenormalisedExtensionTensorModel
public import Phi43.Structure.RenormalisedExtensionAdmissible
public import Phi43.Structure.RenormalisedExtensionFiniteNorm
public import RegularityStructures.Abstract.Model

/-!
# Existence of a renormalised canonical model

This proves the existence part of the canonical and renormalised models
[Hai14, Proposition 8.27, Theorem 8.44, Section 9.2]: the explicit corrected
smooth model satisfies all three clauses of the canonical-model predicate
`Statements.IsRenormalisedCanonicalModel`. No analytic bound on the model is
an input. Uniqueness is not asserted here.
-/

public section

namespace RegularityStructures.Phi43

theorem canonicalRenormalisedModel_isRenormalisedCanonicalModel
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    Statements.IsRenormalisedCanonicalModel N κ noise C
      (canonicalRenormalisedModel N κ noise Cg q hg C) :=
  ⟨canonicalRenormalisedModel_isRealising N κ noise Cg q hg C,
    canonicalRenormalisedModel_regPi_tensor_fMinus N κ noise Cg q hg C,
    canonicalRenormalisedModel_normOn_ne_top N κ noise Cg q hg C⟩

end RegularityStructures.Phi43

end
