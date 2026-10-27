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
# `GlobalPhi43.flowLaw`

The law `P_t(x, ·)` of `u(t,0;x)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The law `P_t(x, ·)` of `u(t, 0; x)`. -/
def flowLaw {η : NegExponent} (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (t : ℝ) (x : HolderBesov η) : Measure (HolderBesov η) :=
  P.map fun ω => u t 0 x ω

end GlobalPhi43

end
