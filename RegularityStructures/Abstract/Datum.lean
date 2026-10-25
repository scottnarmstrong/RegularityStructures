/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Deriv
public import RegularityStructures.Abstract.Datum.Taylor
public import RegularityStructures.Abstract.Datum.SeqTaylor
public import RegularityStructures.Abstract.Datum.HeatBounds
public import RegularityStructures.Abstract.Datum.Combinatorics
public import RegularityStructures.Abstract.Datum.Lift
public import RegularityStructures.Abstract.Datum.LiftCoeff
public import RegularityStructures.Abstract.Datum.LiftMeasurable
public import RegularityStructures.Abstract.Datum.BoundAux
public import RegularityStructures.Abstract.Datum.Bound
public import RegularityStructures.Abstract.Datum.SingularLift
public import RegularityStructures.Abstract.Datum.HeatDeriv1
public import RegularityStructures.Abstract.Datum.HeatSmooth
public import RegularityStructures.Abstract.Datum.HeatFlow
public import RegularityStructures.Abstract.Datum.HeatField
public import RegularityStructures.Abstract.Datum.HeatExt
public import RegularityStructures.Abstract.Datum.HeatExtCont
public import RegularityStructures.Abstract.Datum.HeatLikeExt
public import RegularityStructures.Abstract.Datum.DatumLift

/-!
# The lift of the free heat evolution of an initial datum (aggregator)

[Hai14, Lemma 7.5 and Proposition A.1]: the initial datum enters the fixed point through the
Taylor lift of its free heat evolution.


* `Datum.Deriv`, `Datum.Taylor`, `Datum.SeqTaylor`: partial derivatives on `{t > 0}` and the
  coordinatewise Taylor expansion;
* `Datum.HeatBounds`: derivative bounds from spatial bounds and the heat equation;
* `Datum.Lift*`, `Datum.Bound*`, `Datum.SingularLift`: the Taylor lift into the polynomial sector
  and its singular modelled distribution bounds;
* `Datum.HeatDeriv1`, `Datum.HeatSmooth`, `Datum.HeatFlow`, `Datum.HeatField`: smoothing and
  derivative bounds of `P_t g` for continuous `g`;
* `Datum.HeatExt`, `Datum.HeatExtCont`, `Datum.HeatLikeExt`: `P_t a` for `a ∈ 𝒞^η`;
* `Datum.DatumLift`: the lift `datumLift` and its properties.
-/
