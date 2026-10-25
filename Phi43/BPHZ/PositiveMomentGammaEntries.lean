/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositiveMomentGammaV

/-!
# Random families of renormalised canonical models

`IsRandomPhi43Model N κ ξ C Z`: for every `ω`, `Z ω` is the renormalised canonical model of the
periodic lift of the smooth noise `ξ ω`, whose derivatives of order `≤ 4` grow polynomially.

For the three random symbols `i ∈ {I(Ψ²)Ψ², I(Ψ³)Ψ, I(Ψ³)Ψ²}` below the cutoff `γ'`, the only
nonzero off-diagonal entry `Γ_{yx} e_i (j)` is the `1`-entry of `I(Ψ²)` (for `I(Ψ²)Ψ²`) or of
`I(Ψ³)` (for the other two), with `j` the lower symbol `Ψ²`, `Ψ`, `Ψ²` respectively
(`Phi43.BPHZ.PositiveMomentGammaAlgebra`). For every model of such a random family, with
`C₁ C` the Wick constant, these entries are the increments `v₂(x, y)`, `v₃(x, y)`
(`gammaMap_iPsiSq_one_eq_gammaWickSq`, `gammaMap_iPsiCube_one_eq_gammaWickCube`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The random family `Z ω` consists, for every `ω`, of the renormalised canonical model of the
periodic lift of the smooth noise `ξ ω`, whose derivatives of order `≤ 4` grow polynomially. -/
@[expose] def IsRandomPhi43Model {Ω : Type*} (N : ℕ) (κ : Kappa) (ξ : Ω → SpaceTime → ℝ)
    (C : RenormalisationConstants)
    (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup) : Prop :=
  ∀ ω, IsSmoothOnSpaceTime (ξ ω) ∧ ∃ noise : CanonicalNoise,
    (∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) ∧
    (∃ (Cg : ℝ) (q : ℕ), ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q) ∧
    Statements.IsRenormalisedCanonicalModel N κ noise C (Z ω)

end RegularityStructures.Phi43

end
