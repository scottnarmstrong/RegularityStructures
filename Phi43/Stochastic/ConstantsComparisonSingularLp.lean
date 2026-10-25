/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsCovariance
public import Phi43.Torus.KernelBoundsLocal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Unregularised parabolic singular weights

The homogeneous dimension of `ℝ × T³` for the parabolic size is five.  This file records the
measure-theoretic estimate used for the unregularised order-one remainder and for the
`L^(4/3)` kernel input: a compactly supported weight `s ↦ s⁻ᑫ` is integrable whenever `q < 5`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

/-- The order-`q` singular weight, truncated outside the unit parabolic ball. -/
def constantsComparisonSingularWeight (q : ℝ) (z : SpaceTime) : ℝ :=
  if 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ 1 then
    torusParabolicSize z ^ (-q)
  else 0

theorem measurable_constantsComparisonSingularWeight (q : ℝ) :
    Measurable (constantsComparisonSingularWeight q) := by
  have hs : MeasurableSet {z : SpaceTime |
      0 < torusParabolicSize z ∧ torusParabolicSize z ≤ 1} :=
    (measurableSet_lt measurable_const measurable_torusParabolicSize).inter
      (measurableSet_le measurable_torusParabolicSize measurable_const)
  have hp := (measurable_pos_rpow_extension (-q)).comp measurable_torusParabolicSize
  have hm : Measurable (fun z : SpaceTime =>
      if 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ 1 then
        (if 0 < torusParabolicSize z then torusParabolicSize z ^ (-q) else 0)
      else 0) := Measurable.ite hs hp measurable_const
  convert hm using 1
  funext z
  by_cases hz : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ 1
  · simp [constantsComparisonSingularWeight, hz]
  · simp [constantsComparisonSingularWeight, hz]

theorem nonneg_constantsComparisonSingularWeight (q : ℝ) (z : SpaceTime) :
    0 ≤ constantsComparisonSingularWeight q z := by
  unfold constantsComparisonSingularWeight
  split_ifs with hz
  · exact Real.rpow_nonneg (le_of_lt hz.1) _
  · exact le_rfl

private theorem constantsComparisonSingularWeight_tail
    {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    volume {z : SpaceTime | t < constantsComparisonSingularWeight q z} ≤
      (Ioc (0 : ℝ) 1).indicator (fun _ : ℝ => ENNReal.ofReal 16) t +
        (Ioi (1 : ℝ)).indicator
          (fun t : ℝ => ENNReal.ofReal (16 * t ^ (-(5 / q : ℝ)))) t := by
  by_cases ht1 : t ≤ 1
  · rw [Set.indicator_of_mem (mem_Ioc.mpr ⟨ht, ht1⟩)]
    have hzero : (Ioi (1 : ℝ)).indicator
        (fun t : ℝ => ENNReal.ofReal (16 * t ^ (-(5 / q : ℝ)))) t = 0 := by
      rw [Set.indicator_of_notMem]
      exact not_lt_of_ge ht1
    rw [hzero, add_zero]
    apply (measure_mono ?_).trans
      (by simpa using (volume_torusParabolicBall_le_global (r := (1 : ℝ))
        (by norm_num : (0 : ℝ) ≤ 1)))
    intro z hz
    by_cases hweight : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ 1
    · exact hweight.2
    · have hbad : t < 0 := by
        simpa [constantsComparisonSingularWeight, hweight] using hz
      exact False.elim ((not_lt_of_ge ht.le) hbad)
  · rw [Set.indicator_of_notMem (fun h => ht1 h.2)]
    have ht1' : 1 < t := lt_of_not_ge ht1
    rw [Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht1')]
    simp only [zero_add]
    calc
      volume {z : SpaceTime | t < constantsComparisonSingularWeight q z} ≤
          volume {z : SpaceTime | torusParabolicSize z ≤ t ^ (-(1 / q : ℝ))} := by
        apply measure_mono
        intro z hz
        by_cases hweight : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ 1
        · have hzt : t < torusParabolicSize z ^ (-q) := by
            simpa [constantsComparisonSingularWeight, hweight] using hz
          have hspos : 0 < torusParabolicSize z := hweight.1
          have hsize : torusParabolicSize z < t ^ (-(1 / q : ℝ)) := by
            have hsize' :=
              (Real.lt_rpow_inv_iff_of_neg hspos ht (by linarith : -q < 0)).2 hzt
            convert hsize' using 1
            field_simp
          exact hsize.le
        · have hbad : t < 0 := by
            simpa [constantsComparisonSingularWeight, hweight] using hz
          exact False.elim ((not_lt_of_ge ht.le) hbad)
      _ ≤ ENNReal.ofReal (16 * t ^ (-(5 / q : ℝ))) := by
        have hpow : (t ^ (-(1 / q : ℝ))) ^ (5 : ℕ) =
            t ^ (-(5 / q : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
          congr 1
          field_simp
          norm_num
        calc
          _ ≤ ENNReal.ofReal (16 * (t ^ (-(1 / q : ℝ))) ^ (5 : ℕ)) :=
            volume_torusParabolicBall_le_global
              (r := t ^ (-(1 / q : ℝ))) (by positivity)
          _ = _ := by rw [hpow]

theorem integrable_constantsComparisonSingularWeight
    {q : ℝ} (hq : 0 < q) (hq5 : q < 5) :
    Integrable (constantsComparisonSingularWeight q) := by
  have hf := measurable_constantsComparisonSingularWeight q
  have hnn : 0 ≤ᵐ[volume] constantsComparisonSingularWeight q :=
    Filter.Eventually.of_forall (nonneg_constantsComparisonSingularWeight q)
  apply (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := (volume : Measure SpaceTime))
    (f_nn := hnn) hf.aemeasurable (by norm_num : (0 : ℝ) < 1)
  have htail : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      volume {z : SpaceTime | t < constantsComparisonSingularWeight q z} ≤
        (Ioc (0 : ℝ) 1).indicator (fun _ : ℝ => ENNReal.ofReal 16) t +
          (Ioi (1 : ℝ)).indicator
            (fun t : ℝ => ENNReal.ofReal (16 * t ^ (-(5 / q : ℝ)))) t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with t ht
    exact constantsComparisonSingularWeight_tail hq ht
  have hmajorant := lintegral_mono_ae htail
  have hconst :
      ∫⁻ t in Ioi (0 : ℝ),
          (Ioc (0 : ℝ) 1).indicator (fun _ : ℝ => ENNReal.ofReal 16) t =
        ENNReal.ofReal 16 := by
    rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
    have hset : Ioc (0 : ℝ) 1 ∩ Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.1⟩
    rw [hset, setLIntegral_const, Real.volume_Ioc]
    norm_num
  have htail_nonneg : 0 ≤ᵐ[volume]
      (Ioi (1 : ℝ)).indicator (fun t : ℝ => 16 * t ^ (-(5 / q : ℝ))) := by
    filter_upwards [] with t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht]
      exact mul_nonneg (by norm_num)
        (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _)
    · rw [Set.indicator_of_notMem ht]
      exact le_rfl
  have hexp : -(5 / q : ℝ) < -1 := by
    rw [neg_lt_neg_iff]
    exact (lt_div_iff₀ hq).2 (by linarith)
  have htail_int : Integrable
      ((Ioi (1 : ℝ)).indicator (fun t : ℝ => 16 * t ^ (-(5 / q : ℝ)))) := by
    have hpi : IntegrableOn (fun t : ℝ => 16 * t ^ (-(5 / q : ℝ)))
        (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (a := -(5 / q : ℝ)) (c := (1 : ℝ))
        hexp one_pos).const_mul 16
    exact hpi.integrable_indicator measurableSet_Ioi
  have htail_value :
      ∫⁻ t in Ioi (0 : ℝ),
          (Ioi (1 : ℝ)).indicator
            (fun t : ℝ => ENNReal.ofReal (16 * t ^ (-(5 / q : ℝ)))) t =
        ENNReal.ofReal (16 * (q / (5 - q))) := by
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi (1 : ℝ) ∩ Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
      ext t
      simp only [mem_inter_iff, mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, lt_trans zero_lt_one h⟩
    rw [hset]
    have hE : (fun t : ℝ => ENNReal.ofReal
        ((Ioi (1 : ℝ)).indicator (fun t => 16 * t ^ (-(5 / q : ℝ))) t)) =
        (Ioi (1 : ℝ)).indicator
          (fun t => ENNReal.ofReal (16 * t ^ (-(5 / q : ℝ)))) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
        simp
    calc
      ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (16 * t ^ (-(5 / q : ℝ))) =
          ∫⁻ t, ENNReal.ofReal
            ((Ioi (1 : ℝ)).indicator (fun t => 16 * t ^ (-(5 / q : ℝ))) t) := by
        rw [hE, lintegral_indicator measurableSet_Ioi]
      _ = ENNReal.ofReal (∫ t,
            (Ioi (1 : ℝ)).indicator (fun t => 16 * t ^ (-(5 / q : ℝ))) t) :=
        (ofReal_integral_eq_lintegral_ofReal htail_int htail_nonneg).symm
      _ = ENNReal.ofReal (16 * (q / (5 - q))) := by
        rw [integral_indicator measurableSet_Ioi, integral_const_mul]
        rw [integral_Ioi_rpow_of_lt (c := (1 : ℝ))
          (a := -(5 / q : ℝ)) (by exact hexp) one_pos]
        norm_num
        have hrat : -1 / (-(5 / q) + 1) = q / (5 - q) := by
          field_simp
          rw [show -5 + q = -(5 - q) by ring]
          simp only [one_div, inv_neg, neg_neg]
        rw [hrat]
  have hsum :
      ∫⁻ t in Ioi (0 : ℝ),
          ((Ioc (0 : ℝ) 1).indicator (fun _ : ℝ => ENNReal.ofReal 16) t +
            (Ioi (1 : ℝ)).indicator
              (fun t : ℝ => ENNReal.ofReal (16 * t ^ (-(5 / q : ℝ)))) t) ≤
        ENNReal.ofReal (16 * (1 + q / (5 - q))) := by
    rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioc)]
    rw [hconst, htail_value, ← ENNReal.ofReal_add (by positivity)]
    rw [show 16 + 16 * (q / (5 - q)) = 16 * (1 + q / (5 - q)) by ring]
    positivity
  have hlayer' :
      ∫⁻ z : SpaceTime, ENNReal.ofReal (constantsComparisonSingularWeight q z) =
        ∫⁻ t in Ioi (0 : ℝ),
          volume {z : SpaceTime | t < constantsComparisonSingularWeight q z} := by
    simpa only [Real.rpow_one, sub_self, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      mul_one] using hlayer
  rw [hlayer']
  apply ne_of_lt
  exact (hmajorant.trans hsum).trans_lt ENNReal.ofReal_lt_top

end RegularityStructures.Phi43

end
