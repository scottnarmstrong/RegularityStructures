/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Elementary measurable and order facts for the torus heat kernels

This module records the properties of the heat kernels (2.1)--(2.2) of the statement that follow
directly from the definitions. The fundamental-domain normalization and the locally uniform
Gaussian-series estimates are proved in `RegularityStructures.Torus.HeatKernelIntegral`.
-/

public section

open MeasureTheory Real Set

namespace RegularityStructures

theorem measurable_torusRep : Measurable torusRep := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_subtype_coe.comp <|
    (AddCircle.measurableEquivIco 1 0).measurable.comp (measurable_pi_apply i)

theorem measurable_gaussKernel : Measurable (fun p : ℝ × (Fin 3 → ℝ) => gaussKernel p.1 p.2) := by
  unfold gaussKernel
  have hbase : Measurable (fun p : ℝ × (Fin 3 → ℝ) => 4 * π * p.1) := by
    fun_prop
  have hpow : Measurable (fun p : ℝ × (Fin 3 → ℝ) => (4 * π * p.1) ^ (-(3 : ℝ) / 2)) := by
    have hpiece :
        (fun p : ℝ × (Fin 3 → ℝ) => (4 * π * p.1) ^ (-(3 : ℝ) / 2)) =
          fun p => if 0 < 4 * π * p.1 then
            exp (log (4 * π * p.1) * (-(3 : ℝ) / 2))
          else if 4 * π * p.1 < 0 then
            exp (log (4 * π * p.1) * (-(3 : ℝ) / 2)) *
              cos ((-(3 : ℝ) / 2) * π)
          else 0 := by
      funext p
      split_ifs with hp hn
      · exact Real.rpow_def_of_pos hp _
      · exact Real.rpow_def_of_neg hn _
      · have hz : 4 * π * p.1 = 0 :=
          le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
        rw [hz, Real.zero_rpow]
        norm_num
    rw [hpiece]
    exact Measurable.ite (measurableSet_Ioi.preimage hbase)
      (measurable_exp.comp ((measurable_log.comp hbase).mul measurable_const)) <|
      Measurable.ite (measurableSet_Iio.preimage hbase)
        ((measurable_exp.comp ((measurable_log.comp hbase).mul measurable_const)).mul
          (measurable_cos.comp (measurable_const.mul measurable_const)))
        measurable_const
  have hsq : Measurable (fun p : ℝ × (Fin 3 → ℝ) => sqNorm3 p.2) := by
    unfold sqNorm3
    exact Finset.measurable_fun_sum Finset.univ fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).pow_const 2
  exact hpow.mul <| measurable_exp.comp <|
    hsq.neg.div (measurable_const.mul measurable_fst)

theorem continuous_sqNorm3 : Continuous sqNorm3 := by
  unfold sqNorm3
  exact continuous_finsetSum Finset.univ fun i _ => (continuous_apply i).pow 2

theorem continuous_gaussKernel_fixed {t : ℝ} (ht : 0 < t) :
    Continuous (gaussKernel t) := by
  unfold gaussKernel
  have hbase : 0 < 4 * π * t := by positivity
  have hpref : Continuous (fun _ : (Fin 3 → ℝ) => (4 * π * t) ^ (-(3 : ℝ) / 2)) := by
    exact continuous_const.rpow_const fun _ => Or.inl (ne_of_gt hbase)
  have hden : Continuous (fun _ : (Fin 3 → ℝ) => 4 * t) := continuous_const
  have hden_ne : ∀ y : Fin 3 → ℝ, (4 * t : ℝ) ≠ 0 := by
    intro y
    nlinarith
  have harg : Continuous (fun y : Fin 3 → ℝ => -sqNorm3 y / (4 * t)) :=
    continuous_sqNorm3.neg.div hden hden_ne
  exact hpref.mul (continuous_exp.comp harg)

theorem measurable_heatKernel : Measurable (fun p : ℝ × Torus3 => heatKernel p.1 p.2) := by
  unfold heatKernel
  apply Measurable.tsum
  intro k
  convert measurable_gaussKernel.comp
      (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))
    using 1 <;> rfl

theorem measurable_heatKernel_fixed (t : ℝ) : Measurable (heatKernel t) := by
  convert measurable_heatKernel.comp (measurable_const.prodMk measurable_id) using 1 <;> rfl

theorem heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : Torus3) : 0 ≤ heatKernel t x := by
  unfold heatKernel
  exact tsum_nonneg fun k => gaussKernel_nonneg ht _

theorem measurable_massiveHeatKernel : Measurable massiveHeatKernel := by
  unfold massiveHeatKernel
  apply Measurable.ite
  · exact measurableSet_Ioi.preimage measurable_fst
  · exact (measurable_exp.comp (measurable_neg.comp measurable_fst)).mul
      (measurable_heatKernel.comp (measurable_fst.prodMk measurable_snd))
  · exact measurable_const

theorem massiveHeatKernel_nonneg (z : SpaceTime) : 0 ≤ massiveHeatKernel z := by
  by_cases hz : 0 < z.1
  · simp only [massiveHeatKernel, hz, ite_true]
    exact mul_nonneg (exp_pos _).le (heatKernel_nonneg hz z.2)
  · simp only [massiveHeatKernel, hz, ite_false]
    exact le_rfl

end RegularityStructures

end
