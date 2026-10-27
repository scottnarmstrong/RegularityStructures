/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import RegularityStructures.Torus.HolderBesov
public import RegularityStructures.Probability.WhiteNoise
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.UniformSpace.Completion

/-!
# `GlobalPhi43.heatAt`

`(P_s z)(x)` for `z ∈ 𝒞^η`: the continuous extension of `f ↦ (P_s f)(x)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `(P_s z)(x)` for `z ∈ 𝒞^η` and `s ∈ (0, 1]`: the continuous extension of `f ↦ (P_s f)(x)` from
`C(T³)`. Characterised by `heatAt_toHolderBesov` and
`continuous_heatAt`. -/
def heatAt (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3) : HolderBesov η → ℝ :=
  UniformSpace.Completion.extension fun f : HolderBesovPre η => heatSemigroup s f x

end GlobalPhi43

end
