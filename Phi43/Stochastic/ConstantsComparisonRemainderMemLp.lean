/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonRemainderBound
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RegularityStructures.Analysis.Parabolic.SmoothNorm

/-!
# The order-one remainder in `L⁴`

The local estimate for `R = G - K^sharp` has order one.  Outside the unit parabolic ball the
Hairer kernel vanishes, and the massive kernel has a bounded integrable tail.  Splitting these
two regions gives the `L⁴` input used in the Section 7 comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private def constantsComparisonRLocal (N : ℕ) : SpaceTime → ℝ :=
  {z : SpaceTime | torusParabolicSize z ≤ 1}.indicator (constantsComparisonR N)

private def constantsComparisonRFar (z : SpaceTime) : ℝ :=
  {z : SpaceTime | 1 < torusParabolicSize z}.indicator massiveHeatKernel z

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

private theorem constantsComparison_singularWeight_one_memLp_four :
    MemLp (constantsComparisonSingularWeight 1) (ENNReal.ofReal 4) := by
  have hmeas : AEStronglyMeasurable (constantsComparisonSingularWeight 1)
      (volume : Measure SpaceTime) :=
    (measurable_constantsComparisonSingularWeight 1).aestronglyMeasurable
  have hweight4 := integrable_constantsComparisonSingularWeight
    (q := (4 : ℝ)) (by norm_num) (by norm_num)
  have hpow : Integrable (fun z : SpaceTime =>
      ‖constantsComparisonSingularWeight 1 z‖ ^ (ENNReal.ofReal 4).toReal) := by
    refine hweight4.congr (Filter.Eventually.of_forall ?_)
    intro z
    by_cases hz : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ 1
    · simp only [constantsComparisonSingularWeight, hz, and_self, ite_true,
        Real.norm_eq_abs]
      rw [show (ENNReal.ofReal (4 : ℝ)).toReal = 4 by norm_num]
      rw [abs_of_nonneg (Real.rpow_nonneg hz.1.le _)]
      rw [← Real.rpow_mul hz.1.le]
      congr 1
      ring
    · simp [constantsComparisonSingularWeight, hz]
  exact (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp hpow

private theorem constantsComparisonR_local_memLp_four (N : ℕ) :
    MemLp (constantsComparisonRLocal N) (ENNReal.ofReal 4) := by
  obtain ⟨C, hC, hbound⟩ := constantsComparisonR_orderOne_ae N
  have hweight := constantsComparison_singularWeight_one_memLp_four
  have hmajorant : MemLp (fun z : SpaceTime =>
      C * constantsComparisonSingularWeight 1 z) (ENNReal.ofReal 4) :=
    hweight.const_mul C
  have hlocalMeas : AEStronglyMeasurable (constantsComparisonRLocal N) := by
    exact ((measurable_massiveHeatKernel.sub
      (measurable_constantsComparison_hairerKernelTorus N)).indicator
      (measurableSet_le measurable_torusParabolicSize measurable_const)).aestronglyMeasurable
  have hlocal : ∀ᵐ z : SpaceTime ∂volume,
      ‖constantsComparisonRLocal N z‖ ≤
        C * constantsComparisonSingularWeight 1 z := by
    filter_upwards [hbound,
      @Measure.ae_ne SpaceTime _ volume
        (Measure.IsAddHaarMeasure.nullSingletonClass volume) (0 : SpaceTime)] with z hz hne
    by_cases hsmall : torusParabolicSize z ≤ 1
    · have hzpos : 0 < torusParabolicSize z := by
        exact constantsComparison_torusParabolicSize_pos_of_ne hne
      simp [constantsComparisonRLocal, hsmall, Real.norm_eq_abs]
      have hmain := hz hzpos hsmall
      have hweight : constantsComparisonSingularWeight 1 z =
          torusParabolicSize z ^ (-1 : ℝ) := by
        simp [constantsComparisonSingularWeight, hzpos, hsmall]
      rw [hweight]
      exact hmain
    · simp [constantsComparisonRLocal, hsmall]
      simp [constantsComparisonSingularWeight, hsmall]
  apply hmajorant.of_le hlocalMeas
  filter_upwards [hlocal] with z hz
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC (nonneg_constantsComparisonSingularWeight 1 z))] using hz

private theorem constantsComparisonR_far_memLp_four :
    MemLp constantsComparisonRFar (ENNReal.ofReal 4) := by
  obtain ⟨C, hC, hG⟩ := massiveHeatKernel_global_singular_bound
  have hmeas : AEStronglyMeasurable constantsComparisonRFar
      (volume : Measure SpaceTime) := by
    apply ((measurable_massiveHeatKernel.indicator
      (measurableSet_lt measurable_const measurable_torusParabolicSize)).aestronglyMeasurable)
  have hpow : Integrable (fun z : SpaceTime =>
      ‖constantsComparisonRFar z‖ ^ (ENNReal.ofReal 4).toReal) := by
    have hmajor : Integrable (fun z : SpaceTime =>
        C ^ (3 : ℝ) * massiveHeatKernel z) :=
      integrable_massiveHeatKernel.const_mul _
    apply Integrable.mono' hmajor
    · exact (hmeas.norm.aemeasurable.pow_const _).aestronglyMeasurable
    · filter_upwards [] with z
      rw [show (ENNReal.ofReal (4 : ℝ)).toReal = 4 by norm_num]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      by_cases hz : 1 < torusParabolicSize z
      · have hzpos : 0 < torusParabolicSize z := lt_trans zero_lt_one hz
        have hG' := hG z hzpos
        have hpow : torusParabolicSize z ^ (-(3 : ℝ)) ≤ 1 := by
          exact (Real.rpow_le_rpow_of_nonpos (by norm_num) hz.le
            (by norm_num)).trans_eq (by norm_num)
        have hupper : massiveHeatKernel z ≤ C := by
          calc
            massiveHeatKernel z ≤ C * torusParabolicSize z ^ (-(3 : ℝ)) := hG'
            _ ≤ C := by simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hpow hC
        have hnonneg := massiveHeatKernel_nonneg z
        calc
          ‖constantsComparisonRFar z‖ ^ (4 : ℝ) = massiveHeatKernel z ^ (4 : ℝ) := by
            simp [constantsComparisonRFar, hz, Real.norm_eq_abs,
              abs_of_nonneg hnonneg]
          _ = massiveHeatKernel z ^ ((3 : ℝ) + 1) := by norm_num
          _ = massiveHeatKernel z ^ (3 : ℝ) * massiveHeatKernel z ^ (1 : ℝ) :=
            Real.rpow_add' hnonneg (by norm_num)
          _ = massiveHeatKernel z ^ (3 : ℝ) * massiveHeatKernel z := by
            rw [Real.rpow_one]
          _ ≤ C ^ (3 : ℝ) * massiveHeatKernel z := by
            have hpow3 : massiveHeatKernel z ^ (3 : ℝ) ≤ C ^ (3 : ℝ) :=
              Real.rpow_le_rpow hnonneg hupper (by norm_num)
            exact mul_le_mul_of_nonneg_right hpow3 hnonneg
          _ = C ^ (3 : ℝ) * massiveHeatKernel z := by rfl
      · simp [constantsComparisonRFar, hz]
        exact mul_nonneg (pow_nonneg hC _) (massiveHeatKernel_nonneg z)
  exact (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp hpow

theorem constantsComparisonR_memLp_four (N : ℕ) :
    MemLp (constantsComparisonR N) (ENNReal.ofReal 4) := by
  have hlocal := constantsComparisonR_local_memLp_four N
  have hfar := constantsComparisonR_far_memLp_four
  have hsum : MemLp (fun z : SpaceTime =>
      constantsComparisonRLocal N z + constantsComparisonRFar z) (ENNReal.ofReal 4) :=
    hlocal.add hfar
  obtain ⟨C, hC, hK⟩ :=
    constantsComparison_hairerKernelTorus_abs_le_singularWeight (N := N)
  have hdecomp : ∀ᵐ z : SpaceTime ∂volume,
      constantsComparisonRLocal N z + constantsComparisonRFar z = constantsComparisonR N z := by
    filter_upwards [hK] with z hz
    by_cases hsmall : torusParabolicSize z ≤ 1
    · have hfar : ¬ 1 < torusParabolicSize z := not_lt_of_ge hsmall
      simp [constantsComparisonRLocal, hsmall, constantsComparisonRFar, hfar,
        constantsComparisonR]
    · have hfar : 1 < torusParabolicSize z := lt_of_not_ge hsmall
      have hzero : hairerKernelTorus N z = 0 := by
        have hweight : constantsComparisonSingularWeight 3 z = 0 := by
          simp [constantsComparisonSingularWeight, hsmall]
        have hz0 : |hairerKernelTorus N z| ≤ 0 := by simpa [hweight] using hz
        exact abs_eq_zero.mp (le_antisymm hz0 (abs_nonneg _))
      simp [constantsComparisonRLocal, hsmall, constantsComparisonRFar, hfar,
        constantsComparisonR, hzero]
  exact hsum.ae_eq hdecomp

end RegularityStructures.Phi43

end
