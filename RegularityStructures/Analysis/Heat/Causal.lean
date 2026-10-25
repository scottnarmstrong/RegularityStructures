/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Causal.Bump
public import RegularityStructures.Analysis.Heat.Causal.Basic
public import RegularityStructures.Analysis.Heat.Causal.Moment
public import RegularityStructures.Analysis.Heat.Causal.Support

/-!
# Causal (non-anticipative) polynomial-annihilating decomposition of the heat kernel (facade)

The analogue of `Analysis/Heat/Annihilating` with a correcting bump supported in `{t > 0}`
(`exists_moment_bump_causal`).  For every `N`: `heatKernelR4 = ∑ₙ annShellC N n + annRemainderC N`
away from `0` (`heatKernelR4_eq_tsum_annShellC`), the kernels `annShellC N n (x - y)` satisfy
Assumption 5.1 with `β = 2` (`isRegularisingDecomposition_annShellC`), annihilate polynomials of
parabolic degree `≤ N - 1` (`annihilatesPolynomials_annShellC`), and the shells and remainder
vanish, with all their derivatives, for `t ≤ 0` (`annShellC_eq_zero_of_nonpos`,
`annRemainderC_eq_zero_of_nonpos`, `lineIter_multiDirs_annShellC_eq_zero`).
Source: Hairer, arXiv:1303.5113v4, Lemma 5.5, Theorem 7.1, Lemma 7.7.
-/
