/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.Phi43Box
public import Phi43Statements.Defs.Phi43NoiseDist
public import Phi43.Structure.Abstract
public import RegularityStructures.Probability.ModelKolmogorovNorm
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The distance between lifts

For a horizon `T`, the distance between two lifts `(Z, ψ)` and `(Z', ψ')` is `d_(T) = ‖Z; Z'‖_{γ;
O_{T+1}} + N_(T)(ψ - ψ')`: the distance of the models on the window `phi43Box (T + 1)` at the cutoff
`γ`, plus the distance `phi43NoiseDist` of the potentials. Classical solutions depend continuously
on the lift for this distance (`phi43ClassicalSolution_stoppedContinuity`), as in [Hai14, Corollary
7.12].

Source: [Hai14, Corollary 7.12].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped ENNReal

/-- The distance `d_(T)` between lifted smooth noises: model difference norm on `O_(T+1)` plus
noise distance. -/
def Statements.phi43Dist (κ : RegularityStructures.Phi43.Kappa) (η T : ℝ)
    (Z Z' : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup)
    (ψ ψ' : ℝ → C(RegularityStructures.Torus3, ℝ)) : ℝ≥0∞ :=
  Z.diffNormOn Z' (RegularityStructures.Phi43.gamma κ)
      (RegularityStructures.Phi43.Statements.phi43Box (T + 1)) +
    RegularityStructures.Phi43.Statements.phi43NoiseDist η T ψ ψ'

end RegularityStructures.Phi43

end
