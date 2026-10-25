/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The massive heat potential of a forcing

`ψ` is the stationary massive heat potential `G * f` of `f : ℝ × T³ → ℝ`: for every `(t, x)` the
integral `∫ G((t, x) - w) f(w) dw` converges absolutely, and its value is `ψ t x`. Here
`G(t, x) = 1_{t>0} e^{-t} p_t(x)` is the massive heat kernel `massiveHeatKernel`, so `ψ` solves
`(∂_t - Δ + 1) ψ = f`. For a regularised noise this is the stationary field `Ψ_ε` of the
statement of Theorem A, whose covariance defines the renormalisation constants of its Definition 2.5.

Source: the statement, equation (2.2) and Definition 2.5.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `ψ` is the stationary massive heat potential `G * f`: the defining integral converges
absolutely at every point, and `ψ` is its value. -/
def IsMassivePotential (f : RegularityStructures.SpaceTime → ℝ)
    (ψ : ℝ → C(RegularityStructures.Torus3, ℝ)) : Prop :=
  (∀ (t : ℝ) (x : RegularityStructures.Torus3),
    MeasureTheory.Integrable (fun w : RegularityStructures.SpaceTime =>
      RegularityStructures.massiveHeatKernel ((t, x) - w) * f w)) ∧
  ∀ (t : ℝ) (x : RegularityStructures.Torus3),
    ψ t x = ∫ w : RegularityStructures.SpaceTime,
      RegularityStructures.massiveHeatKernel ((t, x) - w) * f w

end RegularityStructures

end
