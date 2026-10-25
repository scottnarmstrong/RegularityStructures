/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSDiagonal
public import RegularityStructures.Probability.ModelKolmogorovContinuousRandomModel
public import RegularityStructures.Probability.ModelKolmogorovGlobalGammaIncrements

/-!
# Components of the Kolmogorov criterion for models

Exports the diagonal semigroup norm identities and the intrinsic finite-net construction behind
[HS23, Proposition B.3], the measurability of the model norms of random models with continuous
realisations, and the cocycle increments of the Gamma maps. The continuous version and the
coarse/fine scale moment estimates use only local annealed increments and values on the actual index
set; the compact continuous-map-valued criterion is proved for every real moment order at least one,
with an explicit diameter-only constant.

These are ingredients of the Kolmogorov criterion for models [Hai14, Theorem 10.7]. In the semigroup
formulation used here the model norms test against the semigroup `Q` itself, so no transfer to
compactly supported test functions is needed.
-/

public section

end
