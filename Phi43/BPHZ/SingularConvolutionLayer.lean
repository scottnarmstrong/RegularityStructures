/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SingularConvolutionWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Layer-cake estimates for parabolic power weights

Integral bounds `∫ singularLocalWeight p a ≤ 80/(5-p) a^(5-p)` for `0 < p < 5` and
`∫ singularTailWeight p e ≤ 16 p/(p-5) e^(5-p)` for `5 < p`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem singularLocalWeight_nonneg (p a : ℝ) (z : SpaceTime) :
    0 ≤ singularLocalWeight p a z := by
  unfold singularLocalWeight
  split_ifs
  · exact Real.rpow_nonneg (torusParabolicSize_nonneg z) _
  · exact le_rfl

theorem singularTailWeight_nonneg (p e : ℝ) (z : SpaceTime) :
    0 ≤ singularTailWeight p e z := by
  unfold singularTailWeight
  split_ifs
  · exact Real.rpow_nonneg (torusParabolicSize_nonneg z) _
  · exact le_rfl

theorem measurable_singularLocalWeight (p a : ℝ) : Measurable (singularLocalWeight p a) := by
  have hs : MeasurableSet {z : SpaceTime |
      0 < torusParabolicSize z ∧ torusParabolicSize z ≤ a} :=
    (measurableSet_lt measurable_const Phi43.measurable_torusParabolicSize).inter
      (measurableSet_le Phi43.measurable_torusParabolicSize measurable_const)
  exact Measurable.ite hs (Phi43.measurable_torusParabolicSize.pow_const _) measurable_const

theorem measurable_singularTailWeight (p e : ℝ) : Measurable (singularTailWeight p e) := by
  have hs : MeasurableSet {z : SpaceTime | e < torusParabolicSize z} :=
    measurableSet_lt measurable_const Phi43.measurable_torusParabolicSize
  exact Measurable.ite hs (Phi43.measurable_torusParabolicSize.pow_const _) measurable_const

private theorem lintegral_le_two_tails {W : SpaceTime → ℝ} (hW : Measurable W)
    (hnn : ∀ z, 0 ≤ W z) {R : ℝ} (hR : 0 < R) (F G : ℝ → ℝ)
    (hF : ∀ t ∈ Ioc 0 R, volume {z : SpaceTime | t < W z} ≤ ENNReal.ofReal (F t))
    (hG : ∀ t ∈ Ioi R, volume {z : SpaceTime | t < W z} ≤ ENNReal.ofReal (G t)) :
    ∫⁻ z, ENNReal.ofReal (W z) ≤
      (∫⁻ t in Ioc 0 R, ENNReal.ofReal (F t)) + ∫⁻ t in Ioi R, ENNReal.ofReal (G t) := by
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := (volume : Measure SpaceTime))
    (f_nn := Filter.Eventually.of_forall hnn) hW.aemeasurable (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one, sub_self, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
    mul_one] at hlayer
  rw [hlayer, ← Ioc_union_Ioi_eq_Ioi hR.le,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi_same)]
  exact add_le_add (setLIntegral_mono' measurableSet_Ioc hF)
    (setLIntegral_mono' measurableSet_Ioi hG)

private theorem lintegral_Ioc_rpow {R c q : ℝ} (hR : 0 < R) (hq : -1 < q) (hc : 0 ≤ c) :
    ∫⁻ t in Ioc 0 R, ENNReal.ofReal (c * t ^ q) =
      ENNReal.ofReal (c * (R ^ (q + 1) / (q + 1))) := by
  have hint : IntegrableOn (fun t : ℝ => c * t ^ q) (Ioc 0 R) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hq)).const_mul c
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] fun t : ℝ => c * t ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg hc (Real.rpow_nonneg ht.1.le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hq)]
  rw [Real.zero_rpow (by linarith : q + 1 ≠ 0), sub_zero]

private theorem lintegral_Ioi_rpow {R c q : ℝ} (hR : 0 < R) (hq : q < -1) (hc : 0 ≤ c) :
    ∫⁻ t in Ioi R, ENNReal.ofReal (c * t ^ q) =
      ENNReal.ofReal (c * (-(R ^ (q + 1)) / (q + 1))) := by
  have hint : IntegrableOn (fun t : ℝ => c * t ^ q) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt hq hR).const_mul c
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi R)] fun t : ℝ => c * t ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hc (Real.rpow_nonneg (hR.trans ht).le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_Ioi_rpow_of_lt hq hR]

private theorem size_le_of_lt_rpow {s t p : ℝ} (hs : 0 < s) (ht : 0 < t) (hp : 0 < p)
    (h : t < s ^ (-p)) : s ≤ t ^ (-(1 / p)) := by
  have h1 := (Real.lt_rpow_inv_iff_of_neg hs ht (neg_lt_zero.2 hp)).2 h
  have h2 : (-p)⁻¹ = -(1 / p) := by rw [one_div, neg_inv]
  rw [h2] at h1
  exact h1.le

private theorem volume_ball_rpow_le {t p : ℝ} (ht : 0 < t) :
    volume {z : SpaceTime | torusParabolicSize z ≤ t ^ (-(1 / p))} ≤
      ENNReal.ofReal (16 * t ^ (-(5 / p))) := by
  refine (Phi43.volume_torusParabolicBall_le_global (Real.rpow_nonneg ht.le _)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  apply le_of_eq
  congr 2
  push_cast
  ring

theorem lintegral_singularTailWeight_le {p e : ℝ} (hp : 5 < p) (he : 0 < e) :
    ∫⁻ z, ENNReal.ofReal (singularTailWeight p e z) ≤
      ENNReal.ofReal (16 * p / (p - 5) * e ^ (5 - p)) := by
  have hp0 : 0 < p := by linarith
  have hR : 0 < e ^ (-p) := Real.rpow_pos_of_pos he _
  refine (lintegral_le_two_tails (measurable_singularTailWeight p e)
    (singularTailWeight_nonneg p e) hR (fun t => 16 * t ^ (-(5 / p))) (fun _ => 0) ?_ ?_).trans ?_
  · intro t ht
    refine le_trans (measure_mono ?_) (volume_ball_rpow_le (p := p) ht.1)
    intro z hz
    by_cases hze : e < torusParabolicSize z
    · have hzt : t < torusParabolicSize z ^ (-p) := by
        simpa [singularTailWeight, hze] using hz
      exact size_le_of_lt_rpow (he.trans hze) ht.1 hp0 hzt
    · have : t < 0 := by simpa [singularTailWeight, hze] using hz
      exact absurd ht.1 (not_lt.2 this.le)
  · intro t ht
    have hempty : {z : SpaceTime | t < singularTailWeight p e z} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      by_cases hze : e < torusParabolicSize z
      · have h1 : torusParabolicSize z ^ (-p) < e ^ (-p) :=
          Real.rpow_lt_rpow_of_neg he hze (by linarith)
        simp only [singularTailWeight, hze, ite_true]
        exact h1.le.trans (le_of_lt ht)
      · simp only [singularTailWeight, hze, ite_false]
        exact (hR.trans ht).le
    rw [hempty]
    simp
  · rw [lintegral_Ioc_rpow hR (by have : 5 / p < 1 := by rw [div_lt_one hp0]; exact hp
                                  have : 0 < 5 / p := by positivity
                                  linarith) (by norm_num)]
    simp only [lintegral_const, ENNReal.ofReal_zero, add_zero, zero_mul]
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    have h5 : -(5 / p) + 1 = (p - 5) / p := by field_simp; ring
    rw [h5, ← Real.rpow_mul he.le]
    have h6 : -p * ((p - 5) / p) = 5 - p := by field_simp; ring
    rw [h6]
    field_simp

theorem lintegral_singularLocalWeight_le {p a : ℝ} (hp : 0 < p) (hp5 : p < 5) (ha : 0 < a) :
    ∫⁻ z, ENNReal.ofReal (singularLocalWeight p a z) ≤
      ENNReal.ofReal (80 / (5 - p) * a ^ (5 - p)) := by
  have hR : 0 < a ^ (-p) := Real.rpow_pos_of_pos ha _
  have hq : (5 / p : ℝ) > 1 := by rw [gt_iff_lt, lt_div_iff₀ hp]; linarith
  refine (lintegral_le_two_tails (measurable_singularLocalWeight p a)
    (singularLocalWeight_nonneg p a) hR (fun _ => 16 * a ^ 5)
    (fun t => 16 * t ^ (-(5 / p))) ?_ ?_).trans ?_
  · intro t ht
    refine le_trans (measure_mono ?_) (Phi43.volume_torusParabolicBall_le_global ha.le)
    intro z hz
    by_cases hza : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ a
    · exact hza.2
    · have : t < 0 := by simpa [singularLocalWeight, hza] using hz
      exact absurd ht.1 (not_lt.2 this.le)
  · intro t ht
    have htpos : 0 < t := hR.trans ht
    refine le_trans (measure_mono ?_) (volume_ball_rpow_le (p := p) htpos)
    intro z hz
    by_cases hza : 0 < torusParabolicSize z ∧ torusParabolicSize z ≤ a
    · have hzt : t < torusParabolicSize z ^ (-p) := by
        simpa [singularLocalWeight, hza] using hz
      exact size_le_of_lt_rpow hza.1 htpos hp hzt
    · have : t < 0 := by simpa [singularLocalWeight, hza] using hz
      exact absurd htpos (not_lt.2 this.le)
  · rw [lintegral_Ioi_rpow hR (by linarith) (by norm_num)]
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * a ^ 5),
      ← ENNReal.ofReal_add (by positivity) ?_]
    · apply ENNReal.ofReal_le_ofReal
      apply le_of_eq
      have hq5 : -(5 / p) + 1 = (p - 5) / p := by field_simp; ring
      have h1 : (a ^ (-p)) ^ (-(5 / p) + 1) = a ^ (5 - p) := by
        rw [← Real.rpow_mul ha.le]
        congr 1
        field_simp
        ring
      have h2 : a ^ 5 * a ^ (-p) = a ^ (5 - p) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ha]
        congr 1
      rw [h1]
      have hne : (5 : ℝ) - p ≠ 0 := by linarith
      have hne' : -(5 / p) + 1 ≠ 0 := by
        rw [hq5]; exact div_ne_zero (by linarith) hp.ne'
      calc
        16 * a ^ 5 * a ^ (-p) + 16 * (-(a ^ (5 - p)) / (-(5 / p) + 1)) =
            16 * (a ^ 5 * a ^ (-p)) + 16 * (-(a ^ (5 - p)) / (-(5 / p) + 1)) := by ring
        _ = 80 / (5 - p) * a ^ (5 - p) := by
          have hne2 : p - 5 ≠ 0 := by linarith
          have hp0 : p ≠ 0 := hp.ne'
          rw [h2, hq5]
          field_simp
          ring
    · have hneg : -(5 / p) + 1 < 0 := by linarith
      refine mul_nonneg (by norm_num) (div_nonneg_of_nonpos ?_ hneg.le)
      exact neg_nonpos.2 (Real.rpow_nonneg hR.le _)

private theorem integrable_and_integral_le {W : SpaceTime → ℝ} (hW : Measurable W)
    (hnn : ∀ z, 0 ≤ W z) {C : ℝ} (hC : 0 ≤ C)
    (h : ∫⁻ z, ENNReal.ofReal (W z) ≤ ENNReal.ofReal C) :
    Integrable W ∧ ∫ z, W z ≤ C := by
  have hfin : ∫⁻ z, ENNReal.ofReal (W z) < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨⟨hW.aestronglyMeasurable, ?_⟩, ?_⟩
  · simp only [HasFiniteIntegral, Real.enorm_eq_ofReal (hnn _)]
    exact hfin
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hW.aestronglyMeasurable]
    calc
      (∫⁻ z, ENNReal.ofReal (W z)).toReal ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = C := ENNReal.toReal_ofReal hC

theorem integrable_singularLocalWeight {p a : ℝ} (hp : 0 < p) (hp5 : p < 5) (ha : 0 < a) :
    Integrable (singularLocalWeight p a) :=
  (integrable_and_integral_le (measurable_singularLocalWeight p a)
    (singularLocalWeight_nonneg p a)
    (by have := sub_pos.2 hp5; positivity) (lintegral_singularLocalWeight_le hp hp5 ha)).1

theorem integral_singularLocalWeight_le {p a : ℝ} (hp : 0 < p) (hp5 : p < 5) (ha : 0 < a) :
    ∫ z, singularLocalWeight p a z ≤ 80 / (5 - p) * a ^ (5 - p) :=
  (integrable_and_integral_le (measurable_singularLocalWeight p a)
    (singularLocalWeight_nonneg p a)
    (by have := sub_pos.2 hp5; positivity) (lintegral_singularLocalWeight_le hp hp5 ha)).2

theorem integrable_singularTailWeight {p e : ℝ} (hp : 5 < p) (he : 0 < e) :
    Integrable (singularTailWeight p e) :=
  (integrable_and_integral_le (measurable_singularTailWeight p e)
    (singularTailWeight_nonneg p e)
    (by have := sub_pos.2 hp; have : 0 < p := by linarith
        positivity) (lintegral_singularTailWeight_le hp he)).1

theorem integral_singularTailWeight_le {p e : ℝ} (hp : 5 < p) (he : 0 < e) :
    ∫ z, singularTailWeight p e z ≤ 16 * p / (p - 5) * e ^ (5 - p) :=
  (integrable_and_integral_le (measurable_singularTailWeight p e)
    (singularTailWeight_nonneg p e)
    (by have := sub_pos.2 hp; have : 0 < p := by linarith
        positivity) (lintegral_singularTailWeight_le hp he)).2

end RegularityStructures

end
