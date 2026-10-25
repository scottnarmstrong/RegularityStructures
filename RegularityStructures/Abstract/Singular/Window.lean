/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Abstract.Singular.Window.Single

/-!
# Window ("W") layer of the singular chain: entry points (aggregator)

Model bounds `PiBoundOn`/`GammaBoundOn` only on Hairer's window `hairerTimeWindow = [-1, 2] × ℝ³`
plus qualitative growth `Model.HasQualitativeGrowth`. `Basic`: the window, ball lemma, Γ near
base points; `LocalOrder`: local order of `Π_x e_i` on a ball inside the window; `Single`,
`Scaled`: pairing with rescaled / scaled test functions; `Pairing`: general `τ ∈ T_{<γ}`,
linearity, increments; `JCoeff`: bounds for the coefficients of `J(x)`; `Slab`: base points with
`0 ≤ z.1 ≤ 1`. All constants depend only on `𝒯, γ` (and the profile), not on the growth constants.
-/
