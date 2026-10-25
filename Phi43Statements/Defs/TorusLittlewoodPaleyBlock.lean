/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.TorusDyadicFrequencySymbol
public import Phi43Statements.Defs.TorusLPFrequencyBox
public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# The Littlewood–Paley blocks

The `n`-th Littlewood–Paley block `Δ_n f = ∑_k φ_n(k) f̂(k) e_k` of a continuous function `f` on
`T³`, a trigonometric polynomial, with `φ_n = torusDyadicFrequencySymbol n`. It is one of the
definitions of the Littlewood–Paley norm `torusLittlewoodPaleyENorm` of `B^η_{∞,∞}(T³)`, which
`closureNorm_equiv_littlewoodPaley` compares with the norm of the statement. It coincides with
`RegularityStructures.torusLittlewoodPaleyBlock`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The `n`-th Littlewood–Paley block of a continuous function on `T³`. -/
def Statements.torusLittlewoodPaleyBlock (n : ℕ) (f : C(RegularityStructures.Torus3, ℝ)) :
    C(RegularityStructures.Torus3, ℂ) :=
  ∑ k ∈ RegularityStructures.Phi43.Statements.torusLPFrequencyBox n,
    ((RegularityStructures.Phi43.Statements.torusDyadicFrequencySymbol n k : ℂ) *
      UnitAddTorus.mFourierCoeff (fun x : RegularityStructures.Torus3 => (f x : ℂ)) k) •
      UnitAddTorus.mFourier k

end RegularityStructures.Phi43

end
