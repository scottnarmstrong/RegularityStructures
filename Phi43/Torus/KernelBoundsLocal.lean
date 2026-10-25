/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsWeighted
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Local parabolic singular-integral estimate

The estimate in this file is the local `L¹` counterpart of the weighted tail
estimate.  It is used after splitting a covariance convolution into the two
regions where one of its two factors is at least a fixed fraction of the
separation.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric

namespace RegularityStructures

namespace Phi43

def localParabolicWeight (e a : ℝ) (z : SpaceTime) : ℝ :=
  if e < torusParabolicSize z ∧ torusParabolicSize z ≤ a then
    torusParabolicSize z ^ (-(3 : ℝ))
  else 0

theorem measurable_pos_rpow_extension (p : ℝ) :
    Measurable (fun x : ℝ => if 0 < x then x ^ p else 0) := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Ioi 0) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  exact hcont.measurable_piecewise continuousOn_const measurableSet_Ioi

theorem measurable_localParabolicWeight {e a : ℝ} (he : 0 < e) :
    Measurable (localParabolicWeight e a) := by
  change Measurable (fun z : SpaceTime =>
    if e < torusParabolicSize z ∧ torusParabolicSize z ≤ a then
      torusParabolicSize z ^ (-(3 : ℝ))
    else 0)
  have hs : MeasurableSet {z : SpaceTime |
      e < torusParabolicSize z ∧ torusParabolicSize z ≤ a} :=
    (measurableSet_lt measurable_const measurable_torusParabolicSize).inter
      (measurableSet_le measurable_torusParabolicSize measurable_const)
  have hp := (measurable_pos_rpow_extension (-(3 : ℝ))).comp measurable_torusParabolicSize
  have hm : Measurable (fun z : SpaceTime =>
      if e < torusParabolicSize z ∧ torusParabolicSize z ≤ a then
        (if 0 < torusParabolicSize z then torusParabolicSize z ^ (-(3 : ℝ)) else 0)
      else 0) := Measurable.ite hs hp measurable_const
  convert hm using 1
  funext z
  by_cases hz : e < torusParabolicSize z ∧ torusParabolicSize z ≤ a
  · have hzpos : 0 < torusParabolicSize z := lt_of_lt_of_le he hz.1.le
    simp [hz, hzpos]
  · simp [hz]

theorem localParabolicWeight_nonneg {e a : ℝ} (z : SpaceTime) :
    0 ≤ localParabolicWeight e a z := by
  unfold localParabolicWeight
  split_ifs
  · exact Real.rpow_nonneg (torusParabolicSize_nonneg z) _
  · exact le_rfl

private theorem volume_localParabolicWeight_tail_le {e a t : ℝ} (he : 0 < e)
    (ha : 0 < a) (ht : 0 < t) :
    volume {z : SpaceTime | t < localParabolicWeight e a z} ≤
      (Ioc (0 : ℝ) (a ^ (-(3 : ℝ)))).indicator
          (fun _ : ℝ => ENNReal.ofReal (16 * a ^ 5)) t +
        (Ioi (a ^ (-(3 : ℝ)))).indicator
          (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t := by
  by_cases hta : t ≤ a ^ (-(3 : ℝ))
  · rw [Set.indicator_of_mem (mem_Ioc.mpr ⟨ht, hta⟩)]
    have hzero : (Ioi (a ^ (-(3 : ℝ)))).indicator
        (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t = 0 := by
      rw [Set.indicator_of_notMem]
      exact not_lt_of_ge hta
    rw [hzero, add_zero]
    apply le_trans (measure_mono ?_)
      (volume_torusParabolicBall_le_global (by positivity : 0 ≤ a))
    intro z hz
    by_cases hza : e < torusParabolicSize z ∧ torusParabolicSize z ≤ a
    · exact hza.2
    · have hz' : t < 0 := by simpa [localParabolicWeight, hza] using hz
      exact False.elim ((not_lt_of_ge ht.le) hz')
  · have hnot : t ∉ Ioc (0 : ℝ) (a ^ (-(3 : ℝ))) := fun h => hta h.2
    rw [Set.indicator_of_notMem hnot]
    have hmem : t ∈ Ioi (a ^ (-(3 : ℝ))) := lt_of_not_ge hta
    rw [Set.indicator_of_mem hmem]
    simp only [zero_add]
    calc
      volume {z : SpaceTime | t < localParabolicWeight e a z} ≤
          volume {z : SpaceTime | torusParabolicSize z ≤ t ^ (-(1 / 3 : ℝ))} := by
        apply measure_mono
        intro z hz
        by_cases hza : e < torusParabolicSize z ∧ torusParabolicSize z ≤ a
        · have hzt : t < torusParabolicSize z ^ (-(3 : ℝ)) := by
            simpa [localParabolicWeight, hza] using hz
          have hsp : 0 < torusParabolicSize z := lt_of_lt_of_le he hza.1.le
          have hsize : torusParabolicSize z < t ^ (-(1 / 3 : ℝ)) := by
            have hsize' :=
              (Real.lt_rpow_inv_iff_of_neg hsp ht (by norm_num : (-3 : ℝ) < 0)).2 hzt
            convert hsize' using 1; norm_num
          exact hsize.le
        · have hz' : t < 0 := by simpa [localParabolicWeight, hza] using hz
          exact False.elim ((not_lt_of_ge ht.le) hz')
      _ ≤ ENNReal.ofReal (16 * (t ^ (-(1 / 3 : ℝ))) ^ (5 : ℕ)) :=
        volume_torusParabolicBall_le_global (by positivity)
      _ = ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ))) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        norm_num

private theorem integral_rpow_localParabolic_majorant {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (a ^ (-(3 : ℝ))), 16 * t ^ (-(5 / 3 : ℝ)) = 24 * a ^ 2 := by
  have hR : 0 < a ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos ha _
  have hpow : -(5 / 3 : ℝ) < -1 := by norm_num
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hpow hR]
  rw [show -(5 / 3 : ℝ) + 1 = -(2 / 3 : ℝ) by norm_num]
  rw [← Real.rpow_mul ha.le]
  · norm_num [Real.rpow_neg]
    field_simp
    norm_num

theorem integral_localParabolicWeight_le {e a : ℝ} (he : 0 < e) (ha : 0 < a) :
    ∫⁻ z : SpaceTime, ENNReal.ofReal (localParabolicWeight e a z) ≤
      ENNReal.ofReal (40 * a ^ 2) := by
  have hf := measurable_localParabolicWeight (e := e) (a := a) he
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := (volume : Measure SpaceTime))
    (f_nn := Filter.Eventually.of_forall (localParabolicWeight_nonneg (e := e) (a := a)))
    hf.aemeasurable (by norm_num : (0 : ℝ) < 1)
  have htail : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      volume {z : SpaceTime | t < localParabolicWeight e a z} ≤
        (Ioc (0 : ℝ) (a ^ (-(3 : ℝ)))).indicator
            (fun _ : ℝ => ENNReal.ofReal (16 * a ^ 5)) t +
          (Ioi (a ^ (-(3 : ℝ)))).indicator
            (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with t ht
    exact volume_localParabolicWeight_tail_le he ha ht
  have hmajorant := lintegral_mono_ae htail
  have hp_nonneg : 0 ≤ᵐ[volume]
      (Ioi (a ^ (-(3 : ℝ)))).indicator
        (fun t : ℝ => 16 * t ^ (-(5 / 3 : ℝ))) := by
    filter_upwards [] with t
    by_cases ht : t ∈ Ioi (a ^ (-(3 : ℝ)))
    · rw [Set.indicator_of_mem ht]
      exact mul_nonneg (by norm_num)
        (Real.rpow_nonneg (le_of_lt (lt_trans (Real.rpow_pos_of_pos ha _) ht)) _)
    · rw [Set.indicator_of_notMem ht]
      exact le_rfl
  have hp_int : Integrable ((Ioi (a ^ (-(3 : ℝ)))).indicator
      (fun t : ℝ => 16 * t ^ (-(5 / 3 : ℝ)))) := by
    have hpi : IntegrableOn (fun t : ℝ => 16 * t ^ (-(5 / 3 : ℝ)))
        (Ioi (a ^ (-(3 : ℝ)))) :=
      (integrableOn_Ioi_rpow_of_lt (a := -(5 / 3 : ℝ)) (c := a ^ (-(3 : ℝ)))
        (by norm_num) (Real.rpow_pos_of_pos ha _)).const_mul 16
    exact hpi.integrable_indicator measurableSet_Ioi
  have hconst :
      ∫⁻ t in Ioi (0 : ℝ),
          (Ioc (0 : ℝ) (a ^ (-(3 : ℝ)))).indicator
            (fun _ : ℝ => ENNReal.ofReal (16 * a ^ 5)) t =
        ENNReal.ofReal (16 * a ^ 2) := by
    rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
    have hset : Ioc (0 : ℝ) (a ^ (-(3 : ℝ))) ∩ Ioi (0 : ℝ) =
        Ioc (0 : ℝ) (a ^ (-(3 : ℝ))) := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.1⟩
    rw [hset]
    rw [setLIntegral_const, Real.volume_Ioc]
    rw [show a ^ (-(3 : ℝ)) - 0 = a ^ (-(3 : ℝ)) by ring]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * a ^ 5)]
    congr 1
    calc
      16 * a ^ 5 * a ^ (-(3 : ℝ)) =
          16 * (a ^ (-(3 : ℝ)) * a ^ (5 : ℝ)) := by
            rw [← Real.rpow_natCast]
            ring_nf
      _ = 16 * a ^ (-(3 : ℝ) + 5) := by rw [Real.rpow_add ha]
      _ = 16 * a ^ 2 := by norm_num
  have hp :
      ∫⁻ t in Ioi (0 : ℝ),
          (Ioi (a ^ (-(3 : ℝ)))).indicator
            (fun t : ℝ => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t =
        ENNReal.ofReal (24 * a ^ 2) := by
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi (a ^ (-(3 : ℝ))) ∩ Ioi (0 : ℝ) = Ioi (a ^ (-(3 : ℝ))) := by
      ext t
      simp only [mem_inter_iff, mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, lt_trans (Real.rpow_pos_of_pos ha _) h⟩
    rw [hset]
    have hE : (fun t : ℝ => ENNReal.ofReal
        ((Ioi (a ^ (-(3 : ℝ)))).indicator
          (fun t => 16 * t ^ (-(5 / 3 : ℝ))) t)) =
        (Ioi (a ^ (-(3 : ℝ)))).indicator
          (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) := by
      funext t
      by_cases ht : t ∈ Ioi (a ^ (-(3 : ℝ)))
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
        simp
    calc
      ∫⁻ t in Ioi (a ^ (-(3 : ℝ))), ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ))) =
          ∫⁻ t, ENNReal.ofReal
            ((Ioi (a ^ (-(3 : ℝ)))).indicator
              (fun t => 16 * t ^ (-(5 / 3 : ℝ))) t) := by
        rw [hE, lintegral_indicator measurableSet_Ioi]
      _ = ENNReal.ofReal (∫ t,
            (Ioi (a ^ (-(3 : ℝ)))).indicator
              (fun t => 16 * t ^ (-(5 / 3 : ℝ))) t) :=
        (ofReal_integral_eq_lintegral_ofReal hp_int hp_nonneg).symm
      _ = ENNReal.ofReal (24 * a ^ 2) := by
        rw [integral_indicator measurableSet_Ioi, integral_rpow_localParabolic_majorant ha]
  have hsum' :
      ∫⁻ t in Ioi (0 : ℝ),
          ((Ioc (0 : ℝ) (a ^ (-(3 : ℝ)))).indicator
              (fun _ : ℝ => ENNReal.ofReal (16 * a ^ 5)) t +
            (Ioi (a ^ (-(3 : ℝ)))).indicator
              (fun t => ENNReal.ofReal (16 * t ^ (-(5 / 3 : ℝ)))) t) ≤
        ENNReal.ofReal (40 * a ^ 2) := by
    rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioc)]
    calc
      _ = ENNReal.ofReal (16 * a ^ 2) + ENNReal.ofReal (24 * a ^ 2) := by rw [hconst, hp]
      _ ≤ ENNReal.ofReal (40 * a ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 16 * a ^ 2)]
        · apply ENNReal.ofReal_le_ofReal
          ring_nf
          exact le_rfl
        · positivity
  have hlayer' :
      ∫⁻ z : SpaceTime, ENNReal.ofReal (localParabolicWeight e a z) =
        ∫⁻ t in Ioi (0 : ℝ), volume {z : SpaceTime | t < localParabolicWeight e a z} := by
    simpa only [Real.rpow_one, sub_self, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      mul_one] using hlayer
  rw [hlayer']
  exact hmajorant.trans hsum'

end Phi43

end RegularityStructures

end
