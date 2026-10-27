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
# `GlobalPhi43.averagedLaw`

The averaged law `ν_T = T⁻¹ ∫₀ᵀ Law(u(t,0;0)) dt`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The averaged law `ν_T = T⁻¹ ∫₀ᵀ Law(u(t,0;0)) dt`. -/
def averagedLaw {η : NegExponent} (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (T : ℝ) : Measure (HolderBesov η) :=
  (ENNReal.ofReal T)⁻¹ • (volume.restrict (Ioc (0 : ℝ) T)).bind fun t => flowLaw P u t 0

end GlobalPhi43

end
