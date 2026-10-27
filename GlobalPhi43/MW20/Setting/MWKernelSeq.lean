/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.ParabolicRescale
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# `GlobalPhi43.mwKernelSeq`

The finite iterated MW20 kernels `Ψ_{T,n}`. Source: MW20 §2.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The finite iterated kernels: `mwKernelSeq Φ T n = Ψ_{T,n+1} = Φ_{T/2} * Φ_{T/4} * ⋯ * Φ_{T 2^{-(n+1)}}`
(MW20 §2.1), with `*` the convolution on `ℝ × ℝ³`. -/
def mwKernelSeq (Φ : ParabolicSpace → ℝ) (T : ℝ) : ℕ → ParabolicSpace → ℝ
  | 0 => parabolicRescale Φ (T / 2)
  | n + 1 => MeasureTheory.convolution (mwKernelSeq Φ T n) (parabolicRescale Φ (T / 2 ^ (n + 2)))
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

end GlobalPhi43

end
