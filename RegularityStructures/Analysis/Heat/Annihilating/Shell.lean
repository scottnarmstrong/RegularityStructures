/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.ScaledRegularising
public import RegularityStructures.Analysis.Parabolic.MomentBump
public import RegularityStructures.Analysis.Parabolic.MomentBumpExists

/-!
# Polynomial-annihilating shells of the heat kernel

The correcting bump `annBump`, the base kernel `annKernel0 = heatShell 0 - ψ + 2³ ψ(S² ·)` and the
shells `annShell N n = (2^n)^3 K₀(S^{2^n} ·)`, which annihilate polynomials of scaled degree `< N`.

Source: [Hai14, Lemma 5.5 and Assumption 5.4].
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace RegularityStructures

theorem exists_annBump (N : ℕ) :
    ∃ ψ : ParabolicSpace → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ z, 1 < parabolicNorm z → ψ z = 0) ∧
      ∀ k : PolyIndex N, ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * ψ z = annMoment k :=
  exists_moment_bump N annMoment

/-- The correcting bump `ψ`. -/
def annBump (N : ℕ) : ParabolicSpace → ℝ := Classical.choose (exists_annBump N)

/-- The base kernel `K₀ = heatShell 0 - ψ + 2³ ψ(S² ·)`. -/
def annKernel0 (N : ℕ) (z : ParabolicSpace) : ℝ :=
  heatShell 0 z - annBump N z + 2 ^ 3 * annBump N (parabolicDilate 2 z)

/-- The `n`-th polynomial-annihilating shell `(2^n)^3 K₀(S^{2^n} z)`. -/
def annShell (N n : ℕ) (z : ParabolicSpace) : ℝ := scaledShell (annKernel0 N) n z

end RegularityStructures

end
