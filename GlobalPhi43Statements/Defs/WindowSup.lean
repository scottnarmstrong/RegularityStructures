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
# `GlobalPhi43.windowSup`

The all-data window supremum `S_s ∈ [0, ∞]`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The all-data window supremum `S_s(ω) = sup_{x ∈ 𝒞^η} sup_{0<t≤1} √t ‖u(s+t,s;x)(ω)‖_η ∈ [0, ∞]`. -/
def windowSup {η : NegExponent} (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (s : ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  ⨆ x, ⨆ t ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (√t * ‖u (s + t) s x ω‖)

end GlobalPhi43

end
