/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.IsModerateRenormalisedCanonicalModel
public import RegularityStructures.Torus.Basic

/-!
# The renormalised canonical model of a smooth function, with a moderate weight

`Z` is the renormalised canonical model of the smooth function `f` on `ℝ × T³` with constants `C`:
there is a smooth periodic noise whose realisation is the periodic lift of `f`, and `Z` is its
renormalised canonical model (`IsModerateRenormalisedCanonicalModel`, which includes a weighted
bound on the whole space).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- `Z` is the renormalised canonical model of the periodic lift of `f`, with a moderate
weighted bound. -/
def Statements.IsModeratePhi43ModelOf (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (f : RegularityStructures.SpaceTime → ℝ)
    (C : RegularityStructures.Phi43.RenormalisationConstants)
    (Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup) : Prop :=
  ∃ noise : RegularityStructures.Phi43.CanonicalNoise,
    (∀ z : RegularityStructures.ParabolicSpace,
      noise.zeta z = f (z.1, RegularityStructures.torusProj z.2)) ∧
    RegularityStructures.Phi43.Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z

end RegularityStructures.Phi43

end
