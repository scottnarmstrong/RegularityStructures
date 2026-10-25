/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.MomentBump
public import RegularityStructures.Analysis.Heat.Decomposition.Basic
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Polynomial-annihilating modification of the heat shells

Fix `N`.  Following the second half of the proof of [Hai14, Lemma 5.5], let `ψ = annBump N` be a smooth
function supported in the unit parabolic ball with
`(1 - 2^{-2-|k|_𝔰}) ∫ z^k ψ = ∫ z^k heatShell 0` for all `|k|_𝔰 < N`, and set
`K₀ = heatShell 0 - ψ + 2³ ψ(S² ·)`, `annShell N n = (2^n)^3 K₀(S^{2^n} ·)`,
`annRemainder N = heatRemainder + ψ`.  Then `G = ∑ₙ annShell N n + annRemainder N` away from `0`.

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace RegularityStructures

/-- The prescribed moments `∫ z^k heatShell 0 / (1 - 2^{-2-|k|_𝔰})` of the correcting bump. -/
def annMoment {N : ℕ} (k : PolyIndex N) : ℝ :=
  (∫ z, momentMono k.1 z * heatShell 0 z) / (1 - (((2 : ℝ) ^ (2 + multiDeg k.1)))⁻¹)

end RegularityStructures

end
