/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG
public import RegularityStructures.Abstract.Singular.Remainder.GammaG
public import RegularityStructures.Abstract.Singular.Remainder.IncrementG
public import RegularityStructures.Abstract.Singular.Remainder.LipschitzG

/-!
# The smooth remainder lift `R_γ` for growth models (aggregator)

Weighted version of `RegularityStructures.Abstract.Singular.Remainder`: the global model bounds of
`LayerSetting` are replaced by a `Model.GrowthModel` with weights bounded by `Rw` on `timeWindow8`
(`LayerSettingG`); every constant `max 1 CGam * CPi` becomes `max 1 CGam * CPi * Rw ^ 2`. Lemmas
that do not use model bounds are reused from the unweighted files. The remainder is a generic kernel
`r` with `RemKernel r` (`remKernel_annRemainderC N : RemKernel (annRemainderC N)`), and
`Model.remVecG r` is the lift (`= Model.remVec N` for `r = annRemainderC N`).
-/
