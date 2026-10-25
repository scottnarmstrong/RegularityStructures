/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovQFamilyWeightedSemigroup

/-!
# Weighted parabolic Q-family Kolmogorov criterion

`randomParabolicQFamilySup_moment_le_of_global_weighted` converts the global polynomially weighted
pointwise annealed bound into the compact-set supremum moment bound with regularity loss `5 / p`.
Its deterministic inputs are proved from the Q-family identity and the Schwartz kernel bounds.
Jensen is applied before the spatial supremum, which leaves one dimension-five scaling factor
inside the moment estimate.  The intermediate kernel, tail, and endpoint results are also exposed.
-/

@[expose] public section

namespace RegularityStructures

end RegularityStructures

end
