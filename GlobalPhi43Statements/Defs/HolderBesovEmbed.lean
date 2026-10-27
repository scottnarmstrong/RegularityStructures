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
# `GlobalPhi43.holderBesovEmbed`

The canonical continuous map `ι : 𝒞^{η''} → 𝒞^η`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The canonical continuous map `ι : 𝒞^{η''} → 𝒞^η` for `η ≤ η''`, the extension of the identity of
`C(T³)`. Characterised by `holderBesovEmbed_toHolderBesov` and
`continuous_holderBesovEmbed`. -/
def holderBesovEmbed (η η'' : NegExponent) (_h : (η : ℝ) ≤ η'') : HolderBesov η'' → HolderBesov η :=
  UniformSpace.Completion.map fun f : HolderBesovPre η'' => (show HolderBesovPre η from f)

end GlobalPhi43

end
