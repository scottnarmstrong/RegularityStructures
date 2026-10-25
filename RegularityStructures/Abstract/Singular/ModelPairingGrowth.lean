/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Bound
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Single
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Pairing
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Increment

/-!
# Weighted model pairing with scaled test functions (aggregator)

Weighted (`_growth`) layer of `RegularityStructures.Abstract.Singular.ModelPairing`, for a
`Model.GrowthModel` (`PiBoundGrowth`, `GammaBoundGrowth`, moderate weights): the model bound (2.15)
against `φ^λ_x` (`Bound`), single vectors (`Single`), general `τ ∈ T_{<γ}` (`Pairing`), linearity
and increments (`Increment`) and the time-window corollaries (`Window`). The constants carry the
weight `ρΠ(z) ρΓ(z)` at the base point `z`.
-/
