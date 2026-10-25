/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import RegularityStructures.Analysis.Parabolic.Polynomial
public import RegularityStructures.Analysis.Parabolic.TestFunction
public import RegularityStructures.Analysis.Parabolic.Generator
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
public import RegularityStructures.Analysis.Parabolic.SingularKernel
public import RegularityStructures.Analysis.Parabolic.SmoothNorm
public import RegularityStructures.Analysis.Parabolic.DyadicPartition
public import RegularityStructures.Analysis.Parabolic.MomentBump
public import RegularityStructures.Analysis.Parabolic.Lattice
public import RegularityStructures.Analysis.Parabolic.ScaledTest
public import RegularityStructures.Analysis.Heat.Decay
public import RegularityStructures.Analysis.Semigroup.Basic
public import RegularityStructures.Analysis.Semigroup.Operator
public import RegularityStructures.Analysis.Semigroup.Pairing
public import RegularityStructures.Analysis.Semigroup.Consistency
public import RegularityStructures.Analysis.Semigroup.PairingGrowth
public import RegularityStructures.Analysis.Semigroup.Locality
public import RegularityStructures.Analysis.KernelAll
public import RegularityStructures.Analysis.HeatAll
public import RegularityStructures.Analysis.Kernel.Conservative

/-!
# The deterministic analytic core

Aggregator for the `RegularityStructures.Analysis` modules: parabolic geometry on `ℝ⁴`,
regularising semigroups, `Q`-distributions, and the semigroup reconstruction of germs.
-/
