/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.FixedHeatAnnulus
public import GlobalPhi43.Local.FiniteBoundaryKernel

/-! The four actual fixed kernels and cutoff coefficients from spatial IBP. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ContDiff

 def heatBoundaryKernel (k : ParabolicSpace → ℝ) : Option (Fin 3) → ParabolicSpace → ℝ
  | none => k
  | some i => fun p => fderiv ℝ k p (0, Pi.single i 1)

 def heatBoundaryCoefficient (χ : ParabolicSpace → ℝ) : Option (Fin 3) → ParabolicSpace → ℝ
  | none => heatTestGenerator χ
  | some i => fun p => (-2 : ℝ) * fderiv ℝ χ p (0, Pi.single i 1)

 theorem heatBoundaryKernel_contDiff {k : ParabolicSpace → ℝ} (hk : ContDiff ℝ ∞ k)
    (i : Option (Fin 3)) : ContDiff ℝ ∞ (heatBoundaryKernel k i) := by
  cases i with
  | none => exact hk
  | some i => exact (hk.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

 theorem heatBoundaryKernel_hasCompactSupport {k : ParabolicSpace → ℝ} (hk : HasCompactSupport k)
    (i : Option (Fin 3)) : HasCompactSupport (heatBoundaryKernel k i) := by
  cases i with
  | none => exact hk
  | some i => exact hk.fderiv_apply ℝ ((0, Pi.single i 1) : ParabolicSpace)

 theorem heatBoundaryCoefficient_contDiff {χ : ParabolicSpace → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (i : Option (Fin 3)) : ContDiff ℝ ∞ (heatBoundaryCoefficient χ i) := by
  cases i with
  | none => exact heatTestGenerator_contDiff hχ
  | some i =>
    have hd : ContDiff ℝ ∞ (fun p : ParabolicSpace => fderiv ℝ χ p (0, Pi.single i 1)) :=
      (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact contDiff_const.mul hd

 theorem heatBoundaryCoefficient_hasCompactSupport {χ : ParabolicSpace → ℝ} (hχ : HasCompactSupport χ)
    (i : Option (Fin 3)) : HasCompactSupport (heatBoundaryCoefficient χ i) := by
  cases i with
  | none => exact heatTestGenerator_hasCompactSupport hχ
  | some i => exact (hχ.fderiv_apply ℝ ((0, Pi.single i 1) : ParabolicSpace)).mul_left

end GlobalPhi43.Local
