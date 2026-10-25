/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Window layer with pointwise qualitative growth (aggregator)

The `Window` entry lemmas (pairing bounds on `hairerTimeWindow` with constants independent of the
growth data), restated with the *pointwise* qualitative growth `Model.HasQualitativeGrowthAt M γ x`
at the base point instead of the uniform-in-`x` `Model.HasQualitativeGrowth M γ`. The latter is not
implied by a `Model.GrowthModel` (unbounded weights), the former is
(`Model.GrowthModel.hasQualitativeGrowthAt`).
-/
