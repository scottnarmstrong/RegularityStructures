/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsCovariance
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Weighted parabolic volume estimates

The homogeneous dimension of `ℝ × T³` for the parabolic size is five.  This file
records the layer-cake estimate for the truncated kernel `|z|ₛ⁻⁶`, which is the
only non-algebraic input needed for the covariance convolution bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric

namespace RegularityStructures

namespace Phi43

def truncatedParabolicWeight (r : ℝ) (z : SpaceTime) : ℝ :=
  if r < torusParabolicSize z then torusParabolicSize z ^ (-(6 : ℝ)) else 0

theorem measurable_truncatedParabolicWeight {r : ℝ} (hr : 0 < r) :
    Measurable (truncatedParabolicWeight r) := by
  change Measurable (fun z : SpaceTime =>
    if r < torusParabolicSize z then torusParabolicSize z ^ (-(6 : ℝ)) else 0)
  have hset : MeasurableSet {z : SpaceTime | r < torusParabolicSize z} :=
    measurableSet_lt measurable_const measurable_torusParabolicSize
  have hpow : Measurable (fun x : ℝ => if 0 < x then x ^ (-(6 : ℝ)) else 0) := by
    have hcont : ContinuousOn (fun x : ℝ => x ^ (-(6 : ℝ))) (Ioi 0) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    exact hcont.measurable_piecewise continuousOn_const measurableSet_Ioi
  have hpow' := hpow.comp measurable_torusParabolicSize
  have hm : Measurable (fun z : SpaceTime =>
      if r < torusParabolicSize z then
        (if 0 < torusParabolicSize z then torusParabolicSize z ^ (-(6 : ℝ)) else 0)
      else 0) := Measurable.ite hset hpow' measurable_const
  convert hm using 1
  funext z
  by_cases hz : r < torusParabolicSize z
  · have hzpos : 0 < torusParabolicSize z := lt_of_lt_of_le hr (le_of_lt hz)
    simp [hz, hzpos]
  · simp [hz]

theorem truncatedParabolicWeight_nonneg {r : ℝ} (z : SpaceTime) :
    0 ≤ truncatedParabolicWeight r z := by
  unfold truncatedParabolicWeight
  split_ifs
  · exact Real.rpow_nonneg (torusParabolicSize_nonneg z) _
  · exact le_rfl

private theorem volume_truncatedParabolicWeight_tail_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    volume {z : SpaceTime | t < truncatedParabolicWeight r z} ≤
      ENNReal.ofReal (16 * t ^ (-(5 / 6 : ℝ))) := by
  calc
    volume {z : SpaceTime | t < truncatedParabolicWeight r z} ≤
        volume {z : SpaceTime | torusParabolicSize z ≤ t ^ (-(1 / 6 : ℝ))} := by
      apply measure_mono
      intro z hz
      by_cases hzr : r < torusParabolicSize z
      · have hzt : t < torusParabolicSize z ^ (-(6 : ℝ)) := by
          simpa [truncatedParabolicWeight, hzr] using hz
        have hsp : 0 < torusParabolicSize z := lt_of_lt_of_le hr (le_of_lt hzr)
        have hsize : torusParabolicSize z < t ^ (-(1 / 6 : ℝ)) := by
          have hsize' :=
            (Real.lt_rpow_inv_iff_of_neg hsp ht (by norm_num : (-6 : ℝ) < 0)).2 hzt
          convert hsize' using 1; norm_num
        exact hsize.le
      · have hz' : t < 0 := by simpa [truncatedParabolicWeight, hzr] using hz
        exact False.elim ((not_lt_of_ge ht.le) hz')
    _ ≤ ENNReal.ofReal (16 * (t ^ (-(1 / 6 : ℝ))) ^ (5 : ℕ)) :=
      volume_torusParabolicBall_le_global (by positivity)
    _ = ENNReal.ofReal (16 * t ^ (-(5 / 6 : ℝ))) := by
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      norm_num

private theorem volume_truncatedParabolicWeight_tail_empty {r t : ℝ} (hr : 0 < r)
    (ht : r ^ (-(6 : ℝ)) ≤ t) :
    {z : SpaceTime | t < truncatedParabolicWeight r z} = ∅ := by
  ext z
  constructor
  · intro hz
    by_cases hzr : r < torusParabolicSize z
    · have hzt : t < torusParabolicSize z ^ (-(6 : ℝ)) := by
        simpa [truncatedParabolicWeight, hzr] using hz
      have hpow : torusParabolicSize z ^ (-(6 : ℝ)) < r ^ (-(6 : ℝ)) :=
        Real.rpow_lt_rpow_of_neg hr hzr (by norm_num)
      exact False.elim ((not_lt_of_ge ht) (hzt.trans hpow))
    · have htp : 0 < t := lt_of_lt_of_le (Real.rpow_pos_of_pos hr _) ht
      have hz' : t < 0 := by simpa [truncatedParabolicWeight, hzr] using hz
      exact False.elim ((not_lt_of_ge htp.le) hz')
  · simp

private theorem integral_truncatedParabolicWeight_majorant {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioc (0 : ℝ) (r ^ (-(6 : ℝ))),
        16 * t ^ (-(5 / 6 : ℝ)) = 96 / r := by
  have hR : 0 < r ^ (-(6 : ℝ)) := Real.rpow_pos_of_pos hr _
  have hpow : -1 < -(5 / 6 : ℝ) := by norm_num
  rw [← intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hpow)]
  rw [show -(5 / 6 : ℝ) + 1 = 1 / 6 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 6 : ℝ) ≠ 0), sub_zero]
  rw [← Real.rpow_mul (le_of_lt hr)]
  norm_num [Real.rpow_neg_one]
  field_simp
  norm_num

theorem lintegral_truncatedParabolicWeight_le {r : ℝ} (hr : 0 < r) :
    ∫⁻ z : SpaceTime, ENNReal.ofReal (truncatedParabolicWeight r z) ≤
      ENNReal.ofReal (96 / r) := by
  have hf := measurable_truncatedParabolicWeight (r := r) hr
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := (volume : Measure SpaceTime))
    (f_nn := Filter.Eventually.of_forall (truncatedParabolicWeight_nonneg (r := r)))
    hf.aemeasurable (by norm_num : (0 : ℝ) < 1)
  have htail : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      volume {z : SpaceTime | t < truncatedParabolicWeight r z} ≤
        (Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))).indicator
          (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 6 : ℝ)))) t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with t ht
    have htpos : 0 < t := ht
    by_cases htr : t ≤ r ^ (-(6 : ℝ))
    · rw [Set.indicator_of_mem (mem_Ioc.mpr ⟨htpos, htr⟩)]
      exact volume_truncatedParabolicWeight_tail_le hr htpos
    · rw [Set.indicator_of_notMem]
      · rw [volume_truncatedParabolicWeight_tail_empty hr (le_of_not_ge htr)]
        simp
      · simp only [mem_Ioc]
        exact fun h => htr h.2
  have hmajorant := lintegral_mono_ae htail
  have hpow : -1 < -(5 / 6 : ℝ) := by norm_num
  have hnonneg : 0 ≤ᵐ[volume]
      (Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))).indicator
        (fun t : ℝ => 16 * t ^ (-(5 / 6 : ℝ))) := by
    filter_upwards [] with t
    by_cases ht : t ∈ Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))
    · simp only [Set.indicator_of_mem ht]
      exact mul_nonneg (by norm_num)
        (Real.rpow_nonneg (mem_Ioc.mp ht).1.le _)
    · rw [Set.indicator_of_notMem ht]
      exact le_rfl
  have hbase : IntegrableOn (fun t : ℝ => 16 * t ^ (-(5 / 6 : ℝ)))
      (Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (Real.rpow_pos_of_pos hr (-(6 : ℝ))).le).mp
      (intervalIntegral.intervalIntegrable_rpow' hpow) |>.const_mul 16
  have hint : Integrable ((Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))).indicator
      (fun t : ℝ => 16 * t ^ (-(5 / 6 : ℝ)))) := hbase.integrable_indicator measurableSet_Ioc
  have hcalc :
      ∫⁻ t in Ioi (0 : ℝ),
        (Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))).indicator
          (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 6 : ℝ)))) t ≤
        ENNReal.ofReal (96 / r) := by
    rw [lintegral_indicator measurableSet_Ioc]
    rw [Measure.restrict_restrict measurableSet_Ioc]
    have hset : Ioc (0 : ℝ) (r ^ (-(6 : ℝ))) ∩ Ioi (0 : ℝ) =
        Ioc (0 : ℝ) (r ^ (-(6 : ℝ))) := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, h.1⟩
    rw [hset]
    have hE : (fun t : ℝ => ENNReal.ofReal
        ((Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))).indicator
          (fun t => 16 * t ^ (-(5 / 6 : ℝ))) t)) =
        (Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))).indicator
          (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 6 : ℝ)))) := by
      funext t
      by_cases ht : t ∈ Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
        simp
    calc
      ∫⁻ t in Ioc (0 : ℝ) (r ^ (-(6 : ℝ))),
          ENNReal.ofReal (16 * t ^ (-(5 / 6 : ℝ))) =
          ∫⁻ t, ENNReal.ofReal
            ((Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))).indicator
              (fun t => 16 * t ^ (-(5 / 6 : ℝ))) t) := by
        rw [hE, lintegral_indicator measurableSet_Ioc]
      _ = ENNReal.ofReal (∫ t,
            (Ioc (0 : ℝ) (r ^ (-(6 : ℝ)))).indicator
              (fun t => 16 * t ^ (-(5 / 6 : ℝ))) t) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
      _ ≤ ENNReal.ofReal (96 / r) := by
        rw [integral_indicator measurableSet_Ioc, integral_truncatedParabolicWeight_majorant hr]
  have hlayer' :
      ∫⁻ z : SpaceTime, ENNReal.ofReal (truncatedParabolicWeight r z) =
        ∫⁻ t in Ioi (0 : ℝ), volume {a : SpaceTime | t < truncatedParabolicWeight r a} := by
    simpa only [Real.rpow_one, sub_self, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      mul_one] using hlayer
  rw [hlayer']
  exact hmajorant.trans hcalc

end Phi43

end RegularityStructures

end
