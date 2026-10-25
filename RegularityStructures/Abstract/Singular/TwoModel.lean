/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.Basic
public import RegularityStructures.Abstract.Singular.TwoModel.Poly
public import RegularityStructures.Abstract.Singular.TwoModel.Gamma
public import RegularityStructures.Abstract.Singular.TwoModel.Group
public import RegularityStructures.Abstract.Singular.TwoModel.Struct
public import RegularityStructures.Abstract.Singular.TwoModel.Model
public import RegularityStructures.Abstract.Singular.TwoModel.Sector
public import RegularityStructures.Abstract.Singular.TwoModel.Bounds
public import RegularityStructures.Abstract.Singular.TwoModel.Lift
public import RegularityStructures.Abstract.Singular.TwoModel.Integration
public import RegularityStructures.Abstract.Singular.TwoModel.IntegrationData
public import RegularityStructures.Abstract.Singular.TwoModel.PairingLinear
public import RegularityStructures.Abstract.Singular.TwoModel.CoeffLinear
public import RegularityStructures.Abstract.Singular.TwoModel.Realising
public import RegularityStructures.Abstract.Singular.TwoModel.LayerSum
public import RegularityStructures.Abstract.Singular.TwoModel.LatticeSum
public import RegularityStructures.Abstract.Singular.TwoModel.JSum
public import RegularityStructures.Abstract.Singular.TwoModel.Theorem71
public import RegularityStructures.Abstract.Singular.TwoModel.Corollary

/-!
# The difference model (facade)

Imports the modules reducing the two-model half of [Hai14, Theorem 7.1] to the single-model one:
the structure `𝒯⊕`, the model `M⊕`, its polynomial sector, bounds,
measurability and the lift of a pair of functions.
-/
