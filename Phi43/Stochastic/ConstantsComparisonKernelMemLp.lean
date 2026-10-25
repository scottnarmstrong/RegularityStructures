/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonKernelLp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import RegularityStructures.Analysis.Parabolic.SmoothNorm

/-!
# The `L^(4/3)` kernel input

The order-three singularity has fourth power of order four, which is integrable in parabolic
dimension five.  The massive kernel is split into its local singular part and its integrable
bounded tail; the truncated kernel is supported in the local part.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private def constantsComparisonWeightThreeMem : SpaceTime → ℝ :=
  constantsComparisonSingularWeight 3

private theorem constantsComparison_torusParabolicSize_pos_of_ne {z : SpaceTime}
    (hz : z ≠ 0) : 0 < torusParabolicSize z := by
  by_contra hs
  have hs0 : torusParabolicSize z = 0 :=
    le_antisymm (le_of_not_gt hs) (torusParabolicSize_nonneg z)
  have htime : √|z.1| = 0 := by
    unfold torusParabolicSize at hs0
    linarith [Real.sqrt_nonneg |z.1|, torusSpatialNorm_nonneg z.2]
  have hsp : torusSpatialNorm z.2 = 0 := by
    unfold torusParabolicSize at hs0
    linarith [Real.sqrt_nonneg |z.1|, torusSpatialNorm_nonneg z.2]
  have htime' : z.1 = 0 := by
    have hsq := Real.sq_sqrt (abs_nonneg z.1)
    have habs : |z.1| = 0 := by
      calc
        |z.1| = √|z.1| ^ 2 := hsq.symm
        _ = 0 := by rw [htime]; norm_num
    exact abs_eq_zero.mp habs
  have hcenter : torusCenteredRep z.2 = 0 := by
    apply (sqNorm3_eq_zero_iff _).mp
    rw [← torusSpatialNorm_sq, hsp]
    norm_num
  have hrep : torusRep z.2 = 0 := by
    funext i
    have hi := congrFun hcenter i
    unfold torusCenteredRep at hi
    split_ifs at hi with hhalf
    · have hrepIco := torusRep_mem_Ico z.2 i
      simp only [Pi.zero_apply] at hi
      have hi' : torusRep z.2 i = 1 := by linarith
      have hrepIco' := hrepIco
      simp only [mem_Ico] at hrepIco'
      linarith
    · exact hi
  have htorus : z.2 = 0 := by
    rw [← RegularityStructures.PDE.torusProj_torusRep z.2, hrep,
      RegularityStructures.PDE.torusProj_zero]
  exact hz (Prod.ext htime' htorus)

private theorem constantsComparison_weight_three_memLp_fourThirds :
    MemLp constantsComparisonWeightThreeMem (ENNReal.ofReal (4 / 3 : ℝ)) := by
  have hmeas : AEStronglyMeasurable constantsComparisonWeightThreeMem
      (volume : Measure SpaceTime) :=
    (measurable_constantsComparisonSingularWeight 3).aestronglyMeasurable
  have hweight4 := integrable_constantsComparisonSingularWeight
    (q := (4 : ℝ)) (by norm_num) (by norm_num)
  have hpow : Integrable (fun z : SpaceTime =>
      ‖constantsComparisonWeightThreeMem z‖ ^
        (ENNReal.ofReal (4 / 3 : ℝ)).toReal) := by
    refine hweight4.congr (Filter.Eventually.of_forall ?_)
    intro z
    by_cases hz : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ 1
    · simp only [constantsComparisonWeightThreeMem,
        constantsComparisonSingularWeight, hz, and_self, ite_true, Real.norm_eq_abs]
      rw [show (ENNReal.ofReal (4 / 3 : ℝ)).toReal = 4 / 3 by norm_num]
      rw [abs_of_nonneg (Real.rpow_nonneg hz.1.le _), ← Real.rpow_mul hz.1.le]
      congr 1
      ring
    · simp only [constantsComparisonWeightThreeMem,
        constantsComparisonSingularWeight, hz, ite_false]
      rw [show (ENNReal.ofReal (4 / 3 : ℝ)).toReal = 4 / 3 by norm_num]
      simp
  exact (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp hpow

private def constantsComparisonMassiveLocal : SpaceTime → ℝ :=
  {z : SpaceTime | torusParabolicSize z ≤ 1}.indicator massiveHeatKernel

private def constantsComparisonMassiveFar : SpaceTime → ℝ :=
  {z : SpaceTime | 1 < torusParabolicSize z}.indicator massiveHeatKernel

private theorem constantsComparison_massive_local_memLp_fourThirds :
    MemLp constantsComparisonMassiveLocal (ENNReal.ofReal (4 / 3 : ℝ)) := by
  obtain ⟨C, hC, hG⟩ := massiveHeatKernel_global_singular_bound
  have hweight := constantsComparison_weight_three_memLp_fourThirds
  have hmajorant : MemLp (fun z : SpaceTime =>
      C * constantsComparisonWeightThreeMem z)
      (ENNReal.ofReal (4 / 3 : ℝ)) := hweight.const_mul C
  have hmeas : AEStronglyMeasurable constantsComparisonMassiveLocal
      (volume : Measure SpaceTime) := by
    exact ((measurable_massiveHeatKernel.indicator
      (measurableSet_le measurable_torusParabolicSize measurable_const)).aestronglyMeasurable)
  have hbound : ∀ᵐ z : SpaceTime ∂volume,
      ‖constantsComparisonMassiveLocal z‖ ≤
        C * constantsComparisonWeightThreeMem z := by
    filter_upwards [@Measure.ae_ne SpaceTime _ volume
      (Measure.IsAddHaarMeasure.nullSingletonClass volume) (0 : SpaceTime)] with z hne
    by_cases hsmall : torusParabolicSize z ≤ 1
    · have hzpos : 0 < torusParabolicSize z := by
        by_contra hz
        exact False.elim (hz
          (constantsComparison_torusParabolicSize_pos_of_ne (z := z) hne))
      simp [constantsComparisonMassiveLocal, hsmall,
        constantsComparisonWeightThreeMem, constantsComparisonSingularWeight,
        hzpos]
      simpa [Real.norm_eq_abs, abs_of_nonneg (massiveHeatKernel_nonneg z),
        Real.rpow_neg hzpos.le] using hG z hzpos
    · simp [constantsComparisonMassiveLocal, hsmall,
        constantsComparisonWeightThreeMem, constantsComparisonSingularWeight]
  apply hmajorant.of_le hmeas
  filter_upwards [hbound] with z hz
  simpa only [constantsComparisonWeightThreeMem, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC
      (nonneg_constantsComparisonSingularWeight 3 z))] using hz

private theorem constantsComparison_massive_far_memLp_fourThirds :
    MemLp constantsComparisonMassiveFar (ENNReal.ofReal (4 / 3 : ℝ)) := by
  obtain ⟨C, hC, hG⟩ := massiveHeatKernel_global_singular_bound
  have hmeas : AEStronglyMeasurable constantsComparisonMassiveFar
      (volume : Measure SpaceTime) := by
    exact ((measurable_massiveHeatKernel.indicator
      (measurableSet_lt measurable_const measurable_torusParabolicSize)).aestronglyMeasurable)
  have hpow : Integrable (fun z : SpaceTime =>
      ‖constantsComparisonMassiveFar z‖ ^
        (ENNReal.ofReal (4 / 3 : ℝ)).toReal) := by
    have hmajor : Integrable (fun z : SpaceTime =>
        C ^ (1 / 3 : ℝ) * massiveHeatKernel z) :=
      integrable_massiveHeatKernel.const_mul _
    apply Integrable.mono' hmajor
    · exact (hmeas.norm.aemeasurable.pow_const _).aestronglyMeasurable
    · filter_upwards [] with z
      rw [show (ENNReal.ofReal (4 / 3 : ℝ)).toReal = 4 / 3 by norm_num]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      by_cases hz : 1 < torusParabolicSize z
      · have hzpos : 0 < torusParabolicSize z := lt_trans zero_lt_one hz
        have hG' := hG z hzpos
        have hsmall : torusParabolicSize z ^ (-(3 : ℝ)) ≤ 1 := by
          exact (Real.rpow_le_rpow_of_nonpos (by norm_num) hz.le
            (by norm_num)).trans_eq (by norm_num)
        have hupper : massiveHeatKernel z ≤ C := by
          calc
            massiveHeatKernel z ≤ C * torusParabolicSize z ^ (-(3 : ℝ)) := hG'
            _ ≤ C := by simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hsmall hC
        have hnonneg := massiveHeatKernel_nonneg z
        calc
          ‖constantsComparisonMassiveFar z‖ ^ (4 / 3 : ℝ) =
              massiveHeatKernel z ^ (4 / 3 : ℝ) := by
            simp [constantsComparisonMassiveFar, hz, Real.norm_eq_abs,
              abs_of_nonneg hnonneg]
          _ = massiveHeatKernel z ^ (1 / 3 : ℝ) * massiveHeatKernel z := by
            have hadd := Real.rpow_add' hnonneg (by norm_num :
                (1 / 3 : ℝ) + 1 ≠ 0)
            convert hadd using 1 <;> norm_num
          _ ≤ C ^ (1 / 3 : ℝ) * massiveHeatKernel z := by
            have hpow := Real.rpow_le_rpow hnonneg hupper (by norm_num :
              (0 : ℝ) ≤ 1 / 3)
            exact mul_le_mul_of_nonneg_right hpow hnonneg
      · simp [constantsComparisonMassiveFar, hz]
        exact mul_nonneg (Real.rpow_nonneg hC _) (massiveHeatKernel_nonneg z)
  exact (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp hpow

theorem constantsComparison_massiveHeatKernel_memLp_fourThirds :
    MemLp massiveHeatKernel (ENNReal.ofReal (4 / 3 : ℝ)) := by
  have hsum : MemLp (fun z : SpaceTime =>
      constantsComparisonMassiveLocal z + constantsComparisonMassiveFar z)
      (ENNReal.ofReal (4 / 3 : ℝ)) :=
    constantsComparison_massive_local_memLp_fourThirds.add
      constantsComparison_massive_far_memLp_fourThirds
  apply hsum.ae_eq
  filter_upwards [] with z
  by_cases hsmall : torusParabolicSize z ≤ 1
  · simp [constantsComparisonMassiveLocal, hsmall, constantsComparisonMassiveFar,
      not_lt_of_ge hsmall]
  · simp [constantsComparisonMassiveLocal, hsmall, constantsComparisonMassiveFar,
      lt_of_not_ge hsmall]

theorem constantsComparison_hairerKernelTorus_memLp_fourThirds (N : ℕ) :
    MemLp (hairerKernelTorus N) (ENNReal.ofReal (4 / 3 : ℝ)) := by
  obtain ⟨C, hC, hK⟩ :=
    constantsComparison_hairerKernelTorus_abs_le_singularWeight (N := N)
  have hweight := constantsComparison_weight_three_memLp_fourThirds
  have hmajorant : MemLp (fun z : SpaceTime =>
      C * constantsComparisonSingularWeight 3 z)
      (ENNReal.ofReal (4 / 3 : ℝ)) := hweight.const_mul C
  have hmeas : AEStronglyMeasurable (hairerKernelTorus N)
      (volume : Measure SpaceTime) :=
    (measurable_constantsComparison_hairerKernelTorus N).aestronglyMeasurable
  apply hmajorant.of_le hmeas
  filter_upwards [hK] with z hz
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC
      (nonneg_constantsComparisonSingularWeight 3 z))] using hz

theorem constantsComparison_massivePlusHairer_memLp_fourThirds (N : ℕ) :
    MemLp (fun z : SpaceTime => massiveHeatKernel z + hairerKernelTorus N z)
      (ENNReal.ofReal (4 / 3 : ℝ)) :=
  constantsComparison_massiveHeatKernel_memLp_fourThirds.add
    (constantsComparison_hairerKernelTorus_memLp_fourThirds (N := N))

end RegularityStructures.Phi43

end
