/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsLocal
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local integrability of the unregularised order-three singularity

The covariance estimates need the scale-invariant bound
`∫_{|z|ₛ ≤ r} |z|ₛ⁻³ ≤ C r²`.  This is the unregularised version of the shifted local
majorant used by the massive-kernel estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

def constantsComparisonLocalSingularWeight (r : ℝ) (z : SpaceTime) : ℝ :=
  if 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ r then
    torusParabolicSize z ^ (-(3 : ℝ))
  else 0

theorem measurable_constantsComparisonLocalSingularWeight {r : ℝ} (_hr : 0 < r) :
    Measurable (constantsComparisonLocalSingularWeight r) := by
  change Measurable (fun z : SpaceTime =>
    if 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ r then
      torusParabolicSize z ^ (-(3 : ℝ)) else 0)
  have hs : MeasurableSet {z : SpaceTime |
      0 < torusParabolicSize z ∧ torusParabolicSize z ≤ r} :=
    (measurableSet_lt measurable_const measurable_torusParabolicSize).inter
      (measurableSet_le measurable_torusParabolicSize measurable_const)
  have hp := (measurable_pos_rpow_extension (-(3 : ℝ))).comp measurable_torusParabolicSize
  have hm : Measurable (fun z : SpaceTime =>
      if 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ r then
        (if 0 < torusParabolicSize z then torusParabolicSize z ^ (-(3 : ℝ)) else 0) else 0) :=
    Measurable.ite hs hp measurable_const
  convert hm using 1
  funext z
  by_cases hz : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ r
  · simp [hz]
  · simp [hz]

theorem nonneg_constantsComparisonLocalSingularWeight (r : ℝ) (z : SpaceTime) :
    0 ≤ constantsComparisonLocalSingularWeight r z := by
  unfold constantsComparisonLocalSingularWeight
  split_ifs with hz
  · exact Real.rpow_nonneg (le_of_lt hz.1) _
  · exact le_rfl

private theorem constantsComparisonLocalSingularWeight_tail {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) :
    volume {z : SpaceTime | t < constantsComparisonLocalSingularWeight r z} ≤
      (Ioc (0 : ℝ) (r ^ (-(3 : ℝ)))).indicator
          (fun _ : ℝ => ENNReal.ofReal (16 * r ^ 5)) t +
        (Ioi (r ^ (-(3 : ℝ)))).indicator
          (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t := by
  by_cases htr : t ≤ r ^ (-(3 : ℝ))
  · rw [Set.indicator_of_mem (mem_Ioc.mpr ⟨ht, htr⟩)]
    have hzero : (Ioi (r ^ (-(3 : ℝ)))).indicator
        (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t = 0 := by
      rw [Set.indicator_of_notMem]
      exact not_lt_of_ge htr
    rw [hzero, add_zero]
    apply le_trans (measure_mono ?_) (volume_torusParabolicBall_le_global hr.le)
    intro z hz
    by_cases hweight : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ r
    · exact hweight.2
    · have hbad : t < 0 := by
        simpa [constantsComparisonLocalSingularWeight, hweight] using hz
      exact False.elim ((not_lt_of_ge ht.le) hbad)
  · have hmem : t ∈ Ioi (r ^ (-(3 : ℝ))) := lt_of_not_ge htr
    rw [Set.indicator_of_notMem (fun h => htr h.2)]
    rw [Set.indicator_of_mem hmem]
    simp only [zero_add]
    calc
      volume {z : SpaceTime | t < constantsComparisonLocalSingularWeight r z} ≤
          volume {z : SpaceTime | torusParabolicSize z ≤ t ^ (-(1 / 3 : ℝ))} := by
        apply measure_mono
        intro z hz
        by_cases hweight : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ r
        · have hzt : t < torusParabolicSize z ^ (-(3 : ℝ)) := by
            simpa [constantsComparisonLocalSingularWeight, hweight] using hz
          have hsize : torusParabolicSize z < t ^ (-(1 / 3 : ℝ)) := by
            have hsize' :=
              (Real.lt_rpow_inv_iff_of_neg hweight.1 ht
                (by norm_num : (-3 : ℝ) < 0)).2 hzt
            convert hsize' using 1
            norm_num
          exact hsize.le
        · have hbad : t < 0 := by
            simpa [constantsComparisonLocalSingularWeight, hweight] using hz
          exact False.elim ((not_lt_of_ge ht.le) hbad)
      _ ≤ ENNReal.ofReal (16 * (t ^ (-(1 / 3 : ℝ))) ^ 5) :=
        volume_torusParabolicBall_le_global (by positivity)
      _ = ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ))) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        congr 1
        ring_nf

private theorem constantsComparisonLocalSingular_tail_integral {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (r ^ (-(3 : ℝ))), 16 * t ^ (-(5 / 3 : ℝ)) = 24 * r ^ 2 := by
  have hR : 0 < r ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hr _
  have hpow : -(5 / 3 : ℝ) < -1 := by norm_num
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hpow hR]
  rw [show -(5 / 3 : ℝ) + 1 = -(2 / 3 : ℝ) by norm_num]
  rw [← Real.rpow_mul hr.le]
  · norm_num [Real.rpow_neg]
    field_simp
    norm_num

theorem integrable_constantsComparisonLocalSingularWeight {r : ℝ} (hr : 0 < r) :
    Integrable (constantsComparisonLocalSingularWeight r) ∧
      ∫ z : SpaceTime, constantsComparisonLocalSingularWeight r z ≤ 40 * r ^ 2 := by
  have hf := measurable_constantsComparisonLocalSingularWeight hr
  have hnn : 0 ≤ᵐ[volume] constantsComparisonLocalSingularWeight r :=
    Filter.Eventually.of_forall (nonneg_constantsComparisonLocalSingularWeight r)
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul
    (μ := (volume : Measure SpaceTime))
    (f_nn := hnn) hf.aemeasurable (by norm_num : (0 : ℝ) < 1)
  have htail : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      volume {z : SpaceTime | t < constantsComparisonLocalSingularWeight r z} ≤
        (Ioc (0 : ℝ) (r ^ (-(3 : ℝ)))).indicator
            (fun _ : ℝ => ENNReal.ofReal (16 * r ^ 5)) t +
          (Ioi (r ^ (-(3 : ℝ)))).indicator
            (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with t ht
    exact constantsComparisonLocalSingularWeight_tail hr ht
  have hmajorant := lintegral_mono_ae htail
  have htail_nonneg : 0 ≤ᵐ[volume]
      (Ioi (r ^ (-(3 : ℝ)))).indicator
        (fun t : ℝ => 16 * t ^ (-(5 / 3 : ℝ))) := by
    filter_upwards [] with t
    by_cases ht : t ∈ Ioi (r ^ (-(3 : ℝ)))
    · rw [Set.indicator_of_mem ht]
      exact mul_nonneg (by norm_num)
        (Real.rpow_nonneg (le_of_lt (lt_trans (Real.rpow_pos_of_pos hr _) ht)) _)
    · rw [Set.indicator_of_notMem ht]
      exact le_rfl
  have htail_int : Integrable ((Ioi (r ^ (-(3 : ℝ)))).indicator
      (fun t : ℝ => 16 * t ^ (-(5 / 3 : ℝ)))) := by
    have hpi : IntegrableOn (fun t : ℝ => 16 * t ^ (-(5 / 3 : ℝ)))
        (Ioi (r ^ (-(3 : ℝ)))) :=
      (integrableOn_Ioi_rpow_of_lt (a := -(5 / 3 : ℝ))
        (c := r ^ (-(3 : ℝ))) (by norm_num) (Real.rpow_pos_of_pos hr _)).const_mul 16
    exact hpi.integrable_indicator measurableSet_Ioi
  have hconst :
      ∫⁻ t in Ioi (0 : ℝ),
          (Ioc (0 : ℝ) (r ^ (-(3 : ℝ)))).indicator
            (fun _ : ℝ => ENNReal.ofReal (16 * r ^ 5)) t =
        ENNReal.ofReal (16 * r ^ 2) := by
    rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
    have hset : Ioc (0 : ℝ) (r ^ (-(3 : ℝ))) ∩ Ioi (0 : ℝ) =
        Ioc (0 : ℝ) (r ^ (-(3 : ℝ))) := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.1⟩
    rw [hset, setLIntegral_const, Real.volume_Ioc]
    simp only [sub_zero]
    rw [Real.rpow_neg hr.le]
    rw [ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply congrArg ENNReal.ofReal
    field_simp [ne_of_gt hr]
    exact (Real.rpow_natCast r 3).symm
  have htail_value :
      ∫⁻ t in Ioi (0 : ℝ),
          (Ioi (r ^ (-(3 : ℝ)))).indicator
            (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t =
        ENNReal.ofReal (24 * r ^ 2) := by
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi (r ^ (-(3 : ℝ))) ∩ Ioi (0 : ℝ) =
        Ioi (r ^ (-(3 : ℝ))) := by
      ext t
      simp only [mem_inter_iff, mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, lt_trans (Real.rpow_pos_of_pos hr _) h⟩
    rw [hset]
    calc
      ∫⁻ t in Ioi (r ^ (-(3 : ℝ))), ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ))) =
          ∫⁻ t, (Ioi (r ^ (-(3 : ℝ)))).indicator
            (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t := by
        rw [lintegral_indicator measurableSet_Ioi]
      _ = ∫⁻ t, ENNReal.ofReal
            ((Ioi (r ^ (-(3 : ℝ)))).indicator
              (fun t => 16 * t ^ (-(5 / 3 : ℝ))) t) := by
        apply lintegral_congr
        intro t
        by_cases htmem : t ∈ Ioi (r ^ (-(3 : ℝ)))
        · rw [Set.indicator_of_mem htmem, Set.indicator_of_mem htmem]
        · rw [Set.indicator_of_notMem htmem, Set.indicator_of_notMem htmem]
          simp
      _ = ENNReal.ofReal (∫ t,
            (Ioi (r ^ (-(3 : ℝ)))).indicator
              (fun t => 16 * t ^ (-(5 / 3 : ℝ))) t) :=
        (ofReal_integral_eq_lintegral_ofReal htail_int htail_nonneg).symm
      _ = ENNReal.ofReal (24 * r ^ 2) := by
        rw [integral_indicator measurableSet_Ioi]
        exact congrArg ENNReal.ofReal
          (constantsComparisonLocalSingular_tail_integral hr)
  have hlayer' :
      ∫⁻ z : SpaceTime, ENNReal.ofReal (constantsComparisonLocalSingularWeight r z) =
        ∫⁻ t in Ioi (0 : ℝ),
          volume {z : SpaceTime | t < constantsComparisonLocalSingularWeight r z} := by
    simpa only [Real.rpow_one, sub_self, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      mul_one] using hlayer
  have hlintegral_le :
      ∫⁻ z : SpaceTime, ENNReal.ofReal (constantsComparisonLocalSingularWeight r z) ≤
        ENNReal.ofReal (40 * r ^ 2) := by
    rw [hlayer']
    calc
    ∫⁻ t in Ioi (0 : ℝ), volume {z : SpaceTime |
        t < constantsComparisonLocalSingularWeight r z} ≤
        ∫⁻ t in Ioi (0 : ℝ),
          (Ioc (0 : ℝ) (r ^ (-(3 : ℝ)))).indicator
            (fun _ : ℝ => ENNReal.ofReal (16 * r ^ 5)) t +
          (Ioi (r ^ (-(3 : ℝ)))).indicator
            (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t := hmajorant
    _ = ENNReal.ofReal (40 * r ^ 2) := by
      rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioc)]
      rw [hconst, htail_value]
      calc
        ENNReal.ofReal (16 * r ^ 2) + ENNReal.ofReal (24 * r ^ 2) =
            ENNReal.ofReal (16 * r ^ 2 + 24 * r ^ 2) :=
          (ENNReal.ofReal_add (by positivity) (by nlinarith [sq_nonneg r])).symm
        _ = ENNReal.ofReal (40 * r ^ 2) := by congr 1; ring
  have hInt : Integrable (constantsComparisonLocalSingularWeight r) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (measurable_constantsComparisonLocalSingularWeight hr).aestronglyMeasurable hnn).mp
    exact ne_of_lt (hlintegral_le.trans_lt ENNReal.ofReal_lt_top)
  have heq := ofReal_integral_eq_lintegral_ofReal hInt hnn
  have hle : ENNReal.ofReal (∫ z : SpaceTime,
      constantsComparisonLocalSingularWeight r z) ≤ ENNReal.ofReal (40 * r ^ 2) := by
    rw [heq]
    exact hlintegral_le
  refine ⟨hInt, ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle

theorem integral_constantsComparisonLocalSingularWeight_le {r : ℝ} (hr : 0 < r) :
    ∫ z : SpaceTime, constantsComparisonLocalSingularWeight r z ≤ 40 * r ^ 2 := by
  exact (integrable_constantsComparisonLocalSingularWeight hr).2

end RegularityStructures.Phi43

end
