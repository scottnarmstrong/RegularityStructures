/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.TorusLift
public import RegularityStructures.PDE.HeatOp
public import RegularityStructures.PDE.HeatOpBridge
public import RegularityStructures.PDE.Duhamel
public import RegularityStructures.PDE.Gronwall
public import RegularityStructures.PDE.Mild
public import RegularityStructures.PDE.SpatialDeriv
public import RegularityStructures.PDE.UniformTaylor
public import RegularityStructures.PDE.MildDeriv
public import RegularityStructures.PDE.GaussDeriv
public import RegularityStructures.PDE.HeatTime
public import RegularityStructures.PDE.Nonlin
public import RegularityStructures.PDE.Jet
public import RegularityStructures.PDE.DuhamelTime
public import RegularityStructures.PDE.MildTime
public import RegularityStructures.PDE.MildSmooth
public import RegularityStructures.PDE.MaxPrinciple
public import RegularityStructures.PDE.SmoothDense
public import RegularityStructures.PDE.Semigroup

/-!
# Semilinear heat equations on the three-torus

Aggregator for the `RegularityStructures.PDE` modules: the heat operator on `C(T³, E)`, Duhamel
integrals, mild solutions of `∂_t u = Δu + G(t, x, u)` (existence for Lipschitz `G`, uniqueness),
their smoothness for smooth data, and a maximum principle. The Φ⁴₃ modules that use it, which prove
the existence of classical solutions in Lemma 4.1 (W4) of the statement
(`RegularityStructures.Phi43.classicalSolution_exists`), belong to `Phi43`, so this library
aggregator does not depend on `Phi43`.
-/
