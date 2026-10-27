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
public import GlobalPhi43Statements.Defs.HeatAt

/-!
# `GlobalPhi43.extNorm`

The extended norm `𝒩^η_{η'}` on `𝒞^η`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The extended norm `𝒩^η_{η'}(z) = sup_{0<s≤1} s^{-η'/2} sup_x |(P_s z)(x)| ∈ [0, ∞]` on `𝒞^η`. -/
def extNorm (η : NegExponent) (η' : ℝ) (z : HolderBesov η) : ℝ≥0∞ :=
  ⨆ s : Ioc (0 : ℝ) 1, ENNReal.ofReal ((s : ℝ) ^ (-η' / 2)) * ⨆ x, ‖heatAt η s x z‖ₑ

end GlobalPhi43

end
