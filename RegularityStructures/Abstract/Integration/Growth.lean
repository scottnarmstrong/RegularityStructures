/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Analysis.Reflect
public import RegularityStructures.Abstract.Integration.Growth.Analysis.Shell
public import RegularityStructures.Abstract.Integration.Growth.Analysis.Small
public import RegularityStructures.Abstract.Integration.Growth.Analysis.Split
public import RegularityStructures.Abstract.Integration.Growth.Analysis.Linear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.Growth.LocalOrder
public import RegularityStructures.Abstract.Integration.Growth.Bundle
public import RegularityStructures.Abstract.Integration.Growth.KConv
public import RegularityStructures.Abstract.Integration.Growth.Commute

/-!
# Local-order estimates for models of polynomial growth

Aggregator for the `RegularityStructures.Abstract.Integration.Growth` modules: the weighted
ingredients of the multilevel Schauder estimate ([Hai14, Theorem 5.12] with the weights of
[Hos25]). Stationary random models only satisfy bounds weighted by polynomially moderate weights
(`IsModerateWeight ρ p`: `ρ ≥ 1`, `ρ z ≤ ρ y (1 + d(z, y))^p`); the weighted hypotheses on a model
are bundled in `Model.GrowthModel` (`RegularityStructures.Abstract.Integration.Growth.Setting`).

* `Analysis.*`: growth versions of the pairing estimates (`IsLocalOrderGrowth`): reflected test
  functions (`Reflect`), derivative shells `D^k K_n(x − ·)` (`Shell`), shells centred away from
  `x` (`Small`, `Split`), splitting of the pairings with the Taylor kernels (`Linear`). The growth
  factor `(1 + R)^q` is the only change: test functions are supported in a ball of radius `R`.
* `LocalOrder`, `Bundle`: `Π_x e_i` is of local order with growth `p + q`, with constants
  proportional to `ρΠ(x) ρΓ(x)` (`Model.isLocalOrderGrowth_regPi_single_in`,
  `Model.GrowthModel.localGrowth_regPi`);
* `KConv`, `Commute`: the class `KRegularG` of `Q`-families of local order with growth and
  exponents above `-2`, and `Π_x e_i` belongs to it (`Model.GrowthModel.kRegularG_regPi_single`),
  the input of [Hai14, Lemma 5.16] under weighted bounds.
-/
