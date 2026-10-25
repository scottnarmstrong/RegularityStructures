/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Growth
public import RegularityStructures.Abstract.Polynomial.Model.Fubini
public import RegularityStructures.Abstract.Polynomial.Model.Reg
public import RegularityStructures.Abstract.Polynomial.Model.Bounds
public import RegularityStructures.Abstract.Polynomial.Model.Unit

/-!
# The polynomial model (aggregator)

The polynomial model `Π_x X^k = (· - x)^k`, `Γ_{xy} = Γ_{x - y}` on `ℝ⁴` with parabolic scaling,
as a `Model (polynomialStructure N) parabolicSemigroup` [Hai14, Section 2.2, Remark 2.23, (2.20)],
with its model bounds.
-/
