/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.Phi43Box
public import Phi43Statements.Defs.Phi43NoiseSize
public import Phi43.Structure.Abstract
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The size of a lift

For a horizon `T`, the size of a lift `(Z, ψ)` is `S_T = ‖Z‖_{γ; O_{T+1}} + N_(T)(ψ)`: the norm of
the model on the window `phi43Box (T + 1)` at the cutoff `γ`, plus the size `phi43NoiseSize` of
the potential. The existence time of classical solutions is bounded below in terms of the size
(`phi43ClassicalSolution_stoppedContinuity`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped ENNReal

/-- The size `S_T` controlled up to horizon `T`: model norm on `O_(T+1)` plus noise size. -/
def Statements.phi43Size (κ : RegularityStructures.Phi43.Kappa) (η T : ℝ)
    (Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup)
    (ψ : ℝ → C(RegularityStructures.Torus3, ℝ)) : ℝ≥0∞ :=
  Z.normOn (RegularityStructures.Phi43.gamma κ) (RegularityStructures.Phi43.Statements.phi43Box (T + 1)) +
    RegularityStructures.Phi43.Statements.phi43NoiseSize η T ψ

end RegularityStructures.Phi43

end
