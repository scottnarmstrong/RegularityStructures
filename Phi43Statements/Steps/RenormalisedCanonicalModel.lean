/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsModerateRenormalisedCanonicalModel
public import RegularityStructures.Probability.ModelKolmogorovNorm
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Phi43.Steps.RenormalisedCanonicalModel

/-!
# The renormalised canonical model of a smooth noise

Let `noise` be a smooth spatially periodic noise whose derivatives of order at most `4` grow at
most polynomially, and let `C = (C₁, C₂)` be renormalisation constants. Then the renormalised
canonical model `M_C Z(noise)` of the Φ⁴₃ regularity structure exists with the properties of
`IsModerateRenormalisedCanonicalModel`, and any two models with these properties coincide below
the cutoff `γ`. Existence is the construction of the canonical model [Hai14, Proposition 8.27]
followed by the renormalisation [Hai14, (8.34)]. Uniqueness holds because an admissible model is
determined by its realisation on the symbols of negative homogeneity and on the polynomials,
as in the uniqueness part of the extension theorem [Hai14, Theorem 5.14].

Here `κ ∈ (0, 1/16)` fixes the homogeneity `-5/2 - κ` of the noise symbol `Ξ` in the Φ⁴₃ regularity
structure `phi43RegularityStructure κ`, the cutoff of the fixed point is `γ = gamma κ = 1 + 3κ`, and
`N` fixes the truncated heat kernel `annKernel0C N` of the kernel decomposition [Hai14, Assumption
5.4].

In the proof of Theorem A, these are the models to which the deterministic solution theory is
applied: the regularised noise at each scale and for each `ω` is lifted to its renormalised
canonical model.

The proof is `RegularityStructures.Phi43.renormalisedCanonicalModel_existsUnique`,
in the module `Phi43.Steps.RenormalisedCanonicalModel`.

Source: [Hai14, Proposition 8.27, (8.34), Definition 5.9, Theorem 5.14].
-/

public section

namespace RegularityStructures.Phi43

/-- **Renormalised canonical model.** Let `noise` be a smooth periodic noise with
`‖D^k ζ(z)‖ ≤ Cg (1 + |z|)^q` for `k ≤ 4`, and let `C` be renormalisation constants. Then a model
`Z` with `IsModerateRenormalisedCanonicalModel N κ noise C Z` exists, and any two such models
`Z`, `Z'` satisfy `‖Z; Z'‖_{γ; ℝ⁴} = 0` at the cutoff `γ = gamma κ`. -/
theorem Statements.renormalisedCanonicalModel_existsUnique (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (noise : RegularityStructures.Phi43.CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : RegularityStructures.ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + RegularityStructures.parabolicNorm z) ^ q)
    (C : RegularityStructures.Phi43.RenormalisationConstants) :
    (∃ Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
        RegularityStructures.parabolicSemigroup,
      RegularityStructures.Phi43.Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z) ∧
    ∀ Z Z' : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
        RegularityStructures.parabolicSemigroup,
      RegularityStructures.Phi43.Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z →
      RegularityStructures.Phi43.Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z' →
        Z.diffNormOn Z' (RegularityStructures.Phi43.gamma κ) Set.univ = 0 :=
  by exact RegularityStructures.Phi43.renormalisedCanonicalModel_existsUnique N κ noise Cg q hg C

end RegularityStructures.Phi43

end
