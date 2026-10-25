/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Defs
public import RegularityStructures.Abstract.Singular.Remainder.Linear
public import RegularityStructures.Abstract.Singular.Remainder.Sup
public import RegularityStructures.Abstract.Singular.Remainder.Gamma
public import RegularityStructures.Abstract.Singular.Remainder.Increment

/-!
# The smooth remainder lift `R_γ` (aggregator)

[Hai14, (7.7)]: `remPairing` (pairing of the lattice reconstruction with the non-compactly
supported `D^k R(x − ·)`, `R = annRemainderC N`, by level-3 cells) and `remVec`, with summability,
linearity, the sup bound with vanishing `w(x)^{ηK − |k|}`, the increment bound `d^{γ+2−|k|}`,
Lipschitz continuity and measurability on the slab.
-/
