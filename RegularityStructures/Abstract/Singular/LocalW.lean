/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox.TelescopeW
public import RegularityStructures.Abstract.Singular.LatticeApprox.ComparisonW
public import RegularityStructures.Abstract.Singular.Kernel.LinearW

/-!
# Window ("W") local estimates for the lattice reconstruction (aggregator)

Window copies of the lattice/local layer of the singular chain: identities (telescoping,
comparison, linearity) use only a qualitative growth model; the quantitative estimates use the
model bounds on `hairerTimeWindow` at base points of the slab `(0, T]`, `T ≤ 1`, and their
constants carry only `max 1 CGam * CPi`. Main result:
`Model.exists_tendsto_and_abs_latticeRecon_sub_pairing_le_win`.
-/
