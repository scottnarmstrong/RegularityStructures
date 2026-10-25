/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.Schwartz
public import RegularityStructures.Analysis.Kernel.Symbol
public import RegularityStructures.Analysis.Kernel.SymbolScale
public import RegularityStructures.Analysis.Kernel.Quartic
public import RegularityStructures.Analysis.Kernel.Gaussian
public import RegularityStructures.Analysis.Kernel.Parabolic
public import RegularityStructures.Analysis.Kernel.Moments
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Kernel.SymbolDeriv
public import RegularityStructures.Analysis.Kernel.TimeDeriv
public import RegularityStructures.Analysis.Kernel.GeneratorProps
public import RegularityStructures.Analysis.Kernel.GeneratorSymbol
public import RegularityStructures.Analysis.Kernel.GeneratorDeriv
public import RegularityStructures.Analysis.Kernel.GeneratorKernel
public import RegularityStructures.Analysis.Kernel.GeneratorPDE
public import RegularityStructures.Analysis.Kernel.GeneratorIBP
public import RegularityStructures.Analysis.Kernel.GeneratorBridge
public import RegularityStructures.Analysis.Kernel.GeneratorStep
public import RegularityStructures.Analysis.Kernel.GeneratorDiff
public import RegularityStructures.Analysis.Kernel.GeneratorLimit
public import RegularityStructures.Analysis.Kernel.GeneratorLip
public import RegularityStructures.Analysis.Kernel.GeneratorMoment
public import RegularityStructures.Analysis.Kernel.GeneratorIdentity

/-!
# The auxiliary kernel `Q_t` on `ℝ⁴`

Aggregator for `RegularityStructures/Analysis/Kernel/`: the one-dimensional heat and quartic
kernels, their tensor product `parabolicKernel`, and the regularising semigroup
`parabolicSemigroup` adapted to the parabolic scaling `𝔰 = (2, 1, 1, 1)` with order `4`.
-/
