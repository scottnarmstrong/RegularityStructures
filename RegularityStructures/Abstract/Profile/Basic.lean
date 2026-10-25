/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Moment
public import RegularityStructures.Analysis.Heat.Causal.Moment
public import RegularityStructures.Analysis.Heat.Decomposition.Vanishing

/-!
# Kernel profiles for the shells `K_n = scaledShell h n`

The multilevel Schauder machinery of `RegularityStructures.Abstract.Integration` is stated for the
particular decomposition `K_n = annShell N n = scaledShell (annKernel0 N) n` of [Hai14, Lemma 5.5].
Only three properties of the profile `annKernel0 N` are used: it is smooth, supported in the closed
unit parabolic ball, and has vanishing monomial moments of parabolic degree `< N`. We record them in
the structure `ShellProfile`, and show that both `annKernel0 N` and the causal profile
`annKernel0C N` satisfy it. The profile-generic copies of the abstract developments live in
`RegularityStructures.Abstract.Profile`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 5.5.
-/

@[expose] public section

namespace RegularityStructures

open scoped ContDiff in
/-- A kernel profile for the shells `K_n = scaledShell h n`: smooth, supported in the closed unit
parabolic ball, with vanishing moments up to parabolic degree `< N` (cf. [Hai14, Lemma 5.5]). -/
structure ShellProfile (h : ParabolicSpace → ℝ) (N : ℕ) : Prop where
  contDiff : ContDiff ℝ ∞ h
  eq_zero : ∀ z, 1 < parabolicNorm z → h z = 0
  moment : ∀ k : PolyIndex N, ∫ z, monoFn k.1 z * h z = 0

end RegularityStructures

end

public section

namespace RegularityStructures

theorem shellProfile_annKernel0C (N : ℕ) : ShellProfile (annKernel0C N) N where
  contDiff := contDiff_annKernel0C N
  eq_zero _ hz := annKernel0C_eq_zero N hz
  moment k := integral_monoFn_mul_annKernel0C k

end RegularityStructures

end
