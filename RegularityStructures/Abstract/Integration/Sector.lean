/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SectorLocal
public import RegularityStructures.Abstract.Integration.SectorLocalOrder
public import RegularityStructures.Abstract.Integration.Sector.Coeff
public import RegularityStructures.Abstract.Integration.Sector.Commute

/-!
# Multilevel Schauder estimate on a sector (facade)

Aggregator for the sector versions of the exponent sets used in the multilevel Schauder estimate.
The degree condition `-2 < deg j` (all `j` with `deg j < γ`) of [Hai14, Theorem 5.12] is only
needed for the basis vectors `e_j ∈ V`, `V` the sector on which `𝒦_γ` acts: the structure may
contain further basis vectors of degree `≤ -2` outside `V` (the Φ⁴₃ noise symbol of degree
`-5/2 - κ`).

* `SectorLocal`, `SectorLocalOrder`: the basis vectors of `V` below `γ` (`sectorBelow`), the
  exponent sets `degreesBelowIn V γ`, `degreesBelowLeIn V γ a`, and the expansion of `Π_x τ` over
  them (`regPi_eq_sum_sectorBelow`);
* `Sector.Coeff`, `Sector.Commute`: the exponent bounds `degreesBelowLeIn_bounds`,
  `degreesBelowLeIn_bounds_two` used for the coefficients of `J(x)` and for Lemma 5.16.
-/
