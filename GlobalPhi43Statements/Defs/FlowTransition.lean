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
public import GlobalPhi43Statements.Defs.FlowLaw

/-!
# `GlobalPhi43.flowTransition`

The transition operator `(P_t f)(x)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The transition operator `(P_t f)(x) = ∫ f dP_t(x, ·)`. -/
def flowTransition {η : NegExponent} (P : Measure Ω)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (t : ℝ) (f : HolderBesov η → ℝ)
    (x : HolderBesov η) : ℝ :=
  ∫ y, f y ∂flowLaw P u t x

end GlobalPhi43

end
