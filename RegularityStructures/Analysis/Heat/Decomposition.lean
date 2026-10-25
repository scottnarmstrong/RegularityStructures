/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Basic
public import RegularityStructures.Analysis.Heat.Decomposition.LineIter
public import RegularityStructures.Analysis.Heat.Decomposition.Support
public import RegularityStructures.Analysis.Heat.Decomposition.Scaling
public import RegularityStructures.Analysis.Heat.Decomposition.Deriv
public import RegularityStructures.Analysis.Heat.Decomposition.Vanishing
public import RegularityStructures.Analysis.Heat.Decomposition.Moment
public import RegularityStructures.Analysis.Heat.Decomposition.Regularising

/-!
# Dyadic decomposition of the heat kernel (facade)

`heatKernelR4 = ∑ₙ heatShell n + heatRemainder` away from `0`, with `heatRemainder` smooth and
`(x, y) ↦ heatShell n (x - y)` satisfying Assumption 5.1 with `β = 2`
(`isRegularisingDecomposition_heatShell`).  Source: Hairer, arXiv:1303.5113v4, Lemma 5.5.
-/
