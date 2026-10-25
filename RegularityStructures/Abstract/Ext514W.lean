/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.SeriesSmall
public import RegularityStructures.Abstract.Ext514W.IntExt

/-!
# Hairer's extension bounds (5.18) for `Γ`, window version (aggregator)

Window (`_win`) versions of the `Γ` parts of `Ext514` and of the extended-model bounds: bounds of
`Π`, `Γ` at level `γ` only on `hairerTimeWindow` (plus a qualitative growth model) give the
`Γ`-bound of the integrated symbols at level `γ + 2` on `timeSlab 1`, for one model, for the
difference of two models, and for the extended models of `IntExtHyp`.

The `Π`-bound of `I e_i` at level `γ + 2` is *not* provided: `Q_t Π̂_x I e_i (x)` involves the germ at
all points weighted by the non-compactly supported heat kernel `Q_t(x, ·)`, hence the model at times
outside the window, which is not controlled by the window constants.
-/
