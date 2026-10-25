/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Bound
public import RegularityStructures.Analysis.Semigroup.Pairing.Tendsto

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Main

/-!
# Pairing of `Q`-distributions with test functions: local order with growth

Aggregator for `Analysis/Semigroup/PairingGrowth/`: the analogues of `tendsto_integral_pairing`
and `abs_pairing_le` for `IsLocalOrderGrowth` (`tendsto_integral_pairing_of_growth`,
`abs_pairing_le_of_growth`), with right-hand side `2^q C · pairingConst A · (B₀ + B₁) · λ^γ`.
-/
