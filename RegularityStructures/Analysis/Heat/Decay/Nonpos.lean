/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Kernel
public import RegularityStructures.Analysis.Heat.Decomposition.LineIter

/-!
# Local facts about iterated derivatives

* `lineIter_congr_of_isOpen`: iterated derivatives of two functions agreeing on an open set agree
  there.
* `lineIter_heatKernelR4_eq_zero_of_nonpos`: all iterated derivatives of the heat kernel vanish at
  points `(t, x)` with `t ≤ 0` and `x ≠ 0` (where the kernel is smooth but vanishes for `t < 0`).
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem lineIter_congr_of_isOpen {f g : ParabolicSpace → ℝ} {U : Set ParabolicSpace}
    (hU : IsOpen U) (h : ∀ z ∈ U, f z = g z) (L : List ParabolicSpace) :
    ∀ z ∈ U, lineIter L f z = lineIter L g z := by
  induction L with
  | nil => exact h
  | cons d L ih =>
    intro z hz
    have hev : lineIter L f =ᶠ[𝓝 z] lineIter L g :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) fun w hw => ih w hw
    simp only [lineIter_cons, dirDeriv, hev.fderiv_eq]

private theorem contDiffAt_lineIter_heatKernelR4 (L : List ParabolicSpace) {z : ParabolicSpace}
    (hz : 0 < sqNorm3 z.2) : ContDiffAt ℝ ∞ (lineIter L heatKernelR4) z := by
  have hne : ∀ w : ParabolicSpace, 0 < sqNorm3 w.2 → w ≠ 0 := by
    rintro w hw rfl
    simp [sqNorm3] at hw
  induction L generalizing z with
  | nil => exact contDiffAt_heatKernelR4 (hne z hz)
  | cons d L ih =>
    simp only [lineIter_cons]
    exact ((ih hz).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem lineIter_heatKernelR4_eq_zero_of_neg (L : List ParabolicSpace)
    {z : ParabolicSpace} (hz : z.1 < 0) : lineIter L heatKernelR4 z = 0 := by
  induction L generalizing z with
  | nil => exact heatKernelR4_of_nonpos hz.le
  | cons d L ih =>
    have hev : lineIter L heatKernelR4 =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem ((isOpen_lt continuous_fst continuous_const).mem_nhds hz)
        fun w hw => ih hw
    simp only [lineIter_cons, dirDeriv, hev.fderiv_eq]
    simp

theorem lineIter_heatKernelR4_eq_zero_of_nonpos (L : List ParabolicSpace) {z : ParabolicSpace}
    (hz : z.1 ≤ 0) (hx : 0 < sqNorm3 z.2) : lineIter L heatKernelR4 z = 0 := by
  have hc : ContinuousAt (lineIter L heatKernelR4) z :=
    (contDiffAt_lineIter_heatKernelR4 L hx).continuousAt
  have hγ : Tendsto (fun ε : ℝ => ((z.1 - ε, z.2) : ParabolicSpace)) (𝓝[>] 0) (𝓝 z) := by
    have : Continuous fun ε : ℝ => ((z.1 - ε, z.2) : ParabolicSpace) :=
      (continuous_const.sub continuous_id).prodMk continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 := hc.tendsto.comp hγ
  have h2 : Tendsto (fun ε : ℝ => lineIter L heatKernelR4 ((z.1 - ε, z.2) : ParabolicSpace))
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (lineIter_heatKernelR4_eq_zero_of_neg L (by simp only; linarith [Set.mem_Ioi.1 hε])).symm
  exact tendsto_nhds_unique h1 h2

end RegularityStructures

end
