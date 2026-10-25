/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import Phi43Statements.Defs.IsPhi43ModelOf
public import RegularityStructures.Statements.Defs.IsMassivePotential

/-!
# Lifts of a smooth noise

`(Z, ψ)` is the lift of the smooth noise `f` with renormalisation constants `C`: `f` has polynomial
growth (`HasPhi43NoiseGrowth`), `Z` is the renormalised canonical model of `f` with constants `C`
(`IsPhi43ModelOf`), and `ψ` is the massive heat potential of `f` (`IsMassivePotential`). The
solution theory takes a lift as input: the classical solution driven by `f` depends continuously on
`(Z, ψ)`. The variant `IsModeratePhi43Lift` also requires the weighted bound of
`IsModerateRenormalisedCanonicalModel` for the model.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The lifted data of a smooth noise with growth: renormalised canonical model and massive
potential. -/
def Statements.IsPhi43Lift (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (f : RegularityStructures.SpaceTime → ℝ)
    (C : RegularityStructures.Phi43.RenormalisationConstants)
    (Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup)
    (ψ : ℝ → C(RegularityStructures.Torus3, ℝ)) : Prop :=
  RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth f ∧
    RegularityStructures.Phi43.Statements.IsPhi43ModelOf N κ f C Z ∧
    RegularityStructures.IsMassivePotential f ψ

end RegularityStructures.Phi43

end
