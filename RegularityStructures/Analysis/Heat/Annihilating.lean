/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Annihilating.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Annihilating.Moment
public import RegularityStructures.Analysis.Heat.Annihilating.Translate

/-!
# Polynomial-annihilating dyadic decomposition of the heat kernel (facade)

For every `N`, `heatKernelR4 = ∑ₙ annShell N n + annRemainder N` away from `0`
(`heatKernelR4_eq_tsum_annShell`), the kernels `(x, y) ↦ annShell N n (x - y)` satisfy Assumption 5.1
with `β = 2` (`isRegularisingDecomposition_annShell`) and annihilate the polynomials of parabolic
degree `≤ N - 1` (`annihilatesPolynomials_annShell`, Assumption 5.4).
Source: Hairer, arXiv:1303.5113v4, Lemma 5.5.
-/
