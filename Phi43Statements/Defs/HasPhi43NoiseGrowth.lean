/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Smooth noises with polynomial growth

A function `f` on `ℝ × T³` has polynomial growth if the derivatives of order at most `4` of its
spatially periodic lift to `ℝ × ℝ³` are bounded by `C_g (1 + |z|)^q`, with `|z|` the parabolic norm.
This is the class of smooth noises for which the renormalised canonical model is constructed and
estimated with polynomial weights. A regularised noise has this property almost surely.

Source: [Hos25].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- Polynomial growth of the derivatives of order `≤ 4` of the periodic lift:
`‖D^k f(z)‖ ≤ C_g (1 + |z|)^q` for `k ≤ 4`. -/
def Statements.HasPhi43NoiseGrowth (f : RegularityStructures.SpaceTime → ℝ) : Prop :=
  ∃ (Cg : ℝ) (q : ℕ), ∀ k : ℕ, k ≤ 4 → ∀ z : RegularityStructures.ParabolicSpace,
    ‖iteratedFDeriv ℝ k
        (fun w : RegularityStructures.ParabolicSpace => f (w.1, RegularityStructures.torusProj w.2))
        z‖ ≤ Cg * (1 + RegularityStructures.parabolicNorm z) ^ q

end RegularityStructures.Phi43

end
