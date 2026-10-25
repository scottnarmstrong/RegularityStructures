/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGaussian
public import RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Smooth Gaussian derivative bounds on compact positive-time sets

The periodised derivative estimates use the differentiated Euclidean Gaussian as their local
model.  This module records the smoothness of that model and the compact-set bounds for each
iterated Fréchet derivative.  The source estimate is Hairer [Hai14], Assumption 5.1, (5.4).
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace RegularityStructures

abbrev EuclideanSpaceTime : Type := ℝ × (Fin 3 → ℝ)

def gaussKernelSpaceTime (z : EuclideanSpaceTime) : ℝ := gaussKernel z.1 z.2

theorem contDiffOn_gaussKernelSpaceTime :
    ContDiffOn ℝ ∞ gaussKernelSpaceTime
      (Ioi 0 ×ˢ (Set.univ : Set (Fin 3 → ℝ))) := by
  rw [(isOpen_Ioi.prod isOpen_univ).contDiffOn_iff]
  intro z hz
  unfold gaussKernelSpaceTime gaussKernel
  have ht : 0 < z.1 := hz.1
  have hbase : 4 * Real.pi * z.1 ≠ 0 := by positivity
  unfold sqNorm3
  fun_prop (disch := aesop)

end RegularityStructures

end
