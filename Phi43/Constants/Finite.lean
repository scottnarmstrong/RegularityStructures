/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Constants
public import Phi43.ClassicalSolution.PeriodiseRegularity
public import RegularityStructures.Torus.HeatKernelIntegrability
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finiteness of the regularised constants

This is item (W3) of Lemma 4.1 of the statement.  The periodised mollifier is bounded and supported
in a compact time strip, so its translates are square-integrable.  The remaining assertions are
obtained from the integrable massive heat kernel, bounded convolution estimates, and the same
`L¹`--`L∞` argument for the covariance.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

namespace Phi43

theorem integrable_periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) : Integrable (periodise ρ ε) := by
  obtain ⟨C, hC⟩ := bounded_periodise ρ hρ hε
  obtain ⟨a, b, hab⟩ := periodise_eq_zero_outside_time_interval ρ hρ hε
  let K : Set SpaceTime := Set.Icc a b ×ˢ Set.univ
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hKmeas : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hKon : IntegrableOn (periodise ρ ε) K := by
    apply IntegrableOn.of_bound hKcompact.measure_lt_top
      (measurable_periodise ρ hρ).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hC z
  have hkind : Integrable (K.indicator (periodise ρ ε)) :=
    hKon.integrable_indicator hKmeas
  apply hkind.congr
  refine Filter.Eventually.of_forall fun z => ?_
  by_cases hz : z ∈ K
  · simp [hz]
  · have htime : z.1 < a ∨ b < z.1 := by
      have hnot : z.1 ∉ Set.Icc a b := by
        intro hztime
        exact hz ⟨hztime, Set.mem_univ _⟩
      by_cases hleft : z.1 < a
      · exact Or.inl hleft
      · by_cases hright : b < z.1
        · exact Or.inr hright
        · exact False.elim (hnot ⟨le_of_not_gt hleft, le_of_not_gt hright⟩)
    rw [hab z htime]
    simp [hz]

theorem memLp_mollifierAt (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (z : SpaceTime) :
    MemLp (mollifierAt ρ ε z) 2 := by
  obtain ⟨C, hC⟩ := bounded_periodise ρ hρ hε
  obtain ⟨a, b, hab⟩ := periodise_eq_zero_outside_time_interval ρ hρ hε
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right C 0
  have hCD : C ≤ D := le_max_left C 0
  have hbound : ∀ w, |mollifierAt ρ ε z w| ≤ D := by
    intro w
    exact (hC (z - w)).trans hCD
  have hmeas : Measurable (mollifierAt ρ ε z) := by
    unfold mollifierAt
    exact measurable_periodise ρ hρ |>.comp (measurable_const.sub measurable_id)
  let K : Set SpaceTime :=
    Set.Icc (z.1 - b) (z.1 - a) ×ˢ Set.univ
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hKmeas : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hzero : ∀ w ∉ K, mollifierAt ρ ε z w = 0 := by
    intro w hw
    have hwtime : w.1 ∉ Set.Icc (z.1 - b) (z.1 - a) := by
      intro hwt
      exact hw ⟨hwt, Set.mem_univ _⟩
    have hwout : z.1 - w.1 < a ∨ b < z.1 - w.1 := by
      by_cases hleft : w.1 < z.1 - b
      · exact Or.inr (by linarith)
      · by_cases hright : z.1 - a < w.1
        · exact Or.inl (by linarith)
        · exact False.elim (hwtime ⟨le_of_not_gt hleft, le_of_not_gt hright⟩)
    exact hab (z - w) hwout
  have hsq_on : IntegrableOn (fun w => mollifierAt ρ ε z w ^ 2) K := by
    apply IntegrableOn.of_bound hKcompact.measure_lt_top
      (hmeas.pow_const 2).aestronglyMeasurable (D ^ 2)
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (mollifierAt ρ ε z w), hbound w]
  have hsq : Integrable (fun w => mollifierAt ρ ε z w ^ 2) := by
    have hind : Integrable (K.indicator (fun w => mollifierAt ρ ε z w ^ 2)) :=
      hsq_on.integrable_indicator hKmeas
    apply hind.congr
    refine Filter.Eventually.of_forall fun w => ?_
    by_cases hw : w ∈ K
    · simp [hw]
    · simp [hw, hzero w hw]
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hsq

theorem mollifiedKernel_facts (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (mollifiedKernel ρ ε) ∧ Integrable (mollifiedKernel ρ ε) ∧
      ∃ C, ∀ z, |mollifiedKernel ρ ε z| ≤ C := by
  have hG : Integrable massiveHeatKernel := integrable_massiveHeatKernel
  have hP : Integrable (periodise ρ ε) := integrable_periodise ρ hρ hε
  have hPc : Continuous (periodise ρ ε) := continuous_periodise ρ hρ hε
  obtain ⟨C, hC⟩ := bounded_periodise ρ hρ hε
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right C 0
  have hCD : C ≤ D := le_max_left C 0
  have hDbdd : BddAbove (Set.range fun z : SpaceTime => ‖periodise ρ ε z‖) := by
    refine ⟨D, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa only [Real.norm_eq_abs] using (hC z).trans hCD
  have hconv_cont : Continuous
      (MeasureTheory.convolution massiveHeatKernel (periodise ρ ε)
        (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hDbdd.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℝ ℝ) hG hPc
  have hconv_int : Integrable
      (MeasureTheory.convolution massiveHeatKernel (periodise ρ ε)
        (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hG.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hP
  have hconv_eq :
      MeasureTheory.convolution massiveHeatKernel (periodise ρ ε)
          (ContinuousLinearMap.mul ℝ ℝ) volume = mollifiedKernel ρ ε := by
    funext z
    rw [convolution_mul_swap]
    rfl
  have hcont : Continuous (mollifiedKernel ρ ε) := by
    rw [← hconv_eq]
    exact hconv_cont
  have hint : Integrable (mollifiedKernel ρ ε) := by
    rw [← hconv_eq]
    exact hconv_int
  have hbound : ∀ z, |mollifiedKernel ρ ε z| ≤ D := by
    intro z
    have hGz : Integrable (fun w => D * massiveHeatKernel (z - w)) :=
      (integrable_comp_sub_left_spaceTime hG z).const_mul D
    change |∫ w, massiveHeatKernel (z - w) * periodise ρ ε w| ≤ D
    have hnorm : ‖∫ w, massiveHeatKernel (z - w) * periodise ρ ε w‖ ≤
        ∫ w, D * massiveHeatKernel (z - w) := by
      apply norm_integral_le_of_norm_le hGz
      filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (massiveHeatKernel_nonneg (z - w))]
      calc
        massiveHeatKernel (z - w) * |periodise ρ ε w| ≤
            massiveHeatKernel (z - w) * D :=
          mul_le_mul_of_nonneg_left (hC w |>.trans hCD)
            (massiveHeatKernel_nonneg (z - w))
        _ = D * massiveHeatKernel (z - w) := by ring
    rw [Real.norm_eq_abs] at hnorm
    calc
      |∫ w, massiveHeatKernel (z - w) * periodise ρ ε w| ≤
          ∫ w, D * massiveHeatKernel (z - w) := hnorm
      _ = D * ∫ w, massiveHeatKernel (z - w) := integral_const_mul D _
      _ = D := by
        rw [integral_comp_sub_left_spaceTime, integral_massiveHeatKernel]
        ring
  exact ⟨hcont, hint, D, hbound⟩

theorem covariance_facts (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ z, Integrable fun w => mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) ∧
      (Continuous (covariance ρ ε) ∧ ∃ C, ∀ z, |covariance ρ ε z| ≤ C) := by
  rcases mollifiedKernel_facts ρ hρ hε with ⟨hGc, hGi, B, hGB⟩
  let D : ℝ := max B 0
  have hBD : B ≤ D := le_max_left B 0
  have hGbound : ∀ z, |mollifiedKernel ρ ε z| ≤ D := by
    intro z
    exact (hGB z).trans hBD
  have hGone : MemLp (mollifiedKernel ρ ε) 1 := memLp_one_iff_integrable.mpr hGi
  have hGnegc : Continuous (fun z => mollifiedKernel ρ ε (-z)) :=
    hGc.comp continuous_neg
  have hGnegbdd : BddAbove
      (Set.range fun z : SpaceTime => ‖mollifiedKernel ρ ε (-z)‖) := by
    refine ⟨D, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa only [Real.norm_eq_abs] using hGbound (-z)
  have hconv_cont : Continuous
      (MeasureTheory.convolution (mollifiedKernel ρ ε)
        (fun z => mollifiedKernel ρ ε (-z))
        (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hGnegbdd.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℝ ℝ) hGi hGnegc
  have hconv_eq_cov :
      MeasureTheory.convolution (mollifiedKernel ρ ε)
          (fun z => mollifiedKernel ρ ε (-z))
          (ContinuousLinearMap.mul ℝ ℝ) volume = covariance ρ ε := by
    funext z
    rw [convolution_mul_swap]
    symm
    let e : SpaceTime ≃ᵐ SpaceTime :=
      MeasurableEquiv.mk (Homeomorph.neg SpaceTime).toEquiv
    have he : MeasurePreserving (e : SpaceTime → SpaceTime)
        (volume : Measure SpaceTime) volume := by
      simpa [e] using (Measure.measurePreserving_neg (volume : Measure SpaceTime))
    have htrans := he.integral_comp'
      (fun w => mollifiedKernel ρ ε (z - w) * mollifiedKernel ρ ε (-w))
    dsimp [e] at htrans
    simpa [covariance, sub_eq_add_neg] using
      htrans
  have hcovc : Continuous (covariance ρ ε) := by
    rw [← hconv_eq_cov]
    exact hconv_cont
  have hqint : ∀ z, Integrable fun w =>
      mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w := by
    intro z
    have htop : MemLp (fun w => mollifiedKernel ρ ε (z + w)) ⊤ :=
      memLp_top_of_bound
        (hGc.comp (continuous_const.add continuous_id)).aestronglyMeasurable D
        (Filter.Eventually.of_forall fun w => by
          simpa only [Real.norm_eq_abs] using hGbound (z + w))
    have hmul := htop.integrable_mul hGone
    change Integrable ((fun w => mollifiedKernel ρ ε (z + w)) * mollifiedKernel ρ ε)
      (volume : Measure SpaceTime) at hmul
    change Integrable (fun w =>
      mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) (volume : Measure SpaceTime)
    exact hmul
  have hqbound : ∃ C, ∀ z, |covariance ρ ε z| ≤ C := by
    let C : ℝ := D * ∫ w, |mollifiedKernel ρ ε w|
    have hnorm : Integrable (fun w => |mollifiedKernel ρ ε w|) := by
      simpa only [Real.norm_eq_abs] using hGi.norm
    refine ⟨C, ?_⟩
    intro z
    have hdom : Integrable (fun w => D * |mollifiedKernel ρ ε w|) :=
      hnorm.const_mul D
    have hq := hqint z
    rw [covariance]
    calc
      |∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
          ∫ w, |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ w, D * |mollifiedKernel ρ ε w| := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          hdom (Filter.Eventually.of_forall fun w => by
            change |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
              D * |mollifiedKernel ρ ε w|
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hGbound (z + w))
              (abs_nonneg (mollifiedKernel ρ ε w)))
      _ = C := by
        rw [integral_const_mul]
  exact ⟨hqint, hcovc, hqbound⟩

theorem constants_finite (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) 1) :
    Integrable massiveHeatKernel ∧
      (∀ z, MemLp (mollifierAt ρ ε z) 2) ∧
      (∀ z, Integrable fun w => massiveHeatKernel (z - w) * periodise ρ ε w) ∧
      (Continuous (mollifiedKernel ρ ε) ∧ Integrable (mollifiedKernel ρ ε) ∧
        ∃ C, ∀ z, |mollifiedKernel ρ ε z| ≤ C) ∧
      (∀ z, Integrable fun w => mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) ∧
      (Continuous (covariance ρ ε) ∧ ∃ C, ∀ z, |covariance ρ ε z| ≤ C) ∧
      Integrable (fun z => mollifiedKernel ρ ε z ^ 2) ∧
      Integrable fun z => massiveHeatKernel z * covariance ρ ε z ^ 2 := by
  have hεpos : 0 < ε := hε.1
  have hG : Integrable massiveHeatKernel := integrable_massiveHeatKernel
  have hLp : ∀ z, MemLp (mollifierAt ρ ε z) 2 :=
    fun z => memLp_mollifierAt ρ hρ hεpos z
  obtain ⟨CP, hCP⟩ := bounded_periodise ρ hρ hεpos
  let DP : ℝ := max CP 0
  have hCPD : CP ≤ DP := le_max_left CP 0
  have hPtop : MemLp (periodise ρ ε) ⊤ :=
    memLp_top_of_bound (measurable_periodise ρ hρ).aestronglyMeasurable DP
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using (hCP z).trans hCPD)
  have hGconv : ∀ z, Integrable fun w =>
      massiveHeatKernel (z - w) * periodise ρ ε w := by
    intro z
    have hGz : MemLp (fun w => massiveHeatKernel (z - w)) 1 :=
      memLp_one_iff_integrable.mpr (integrable_comp_sub_left_spaceTime hG z)
    have hmul := hGz.integrable_mul hPtop
    change Integrable ((fun w => massiveHeatKernel (z - w)) * periodise ρ ε)
      (volume : Measure SpaceTime) at hmul
    change Integrable (fun w => massiveHeatKernel (z - w) * periodise ρ ε w)
      (volume : Measure SpaceTime)
    exact hmul
  rcases mollifiedKernel_facts ρ hρ hεpos with ⟨hMc, hMi, BM, hMB⟩
  have hMbound : ∀ z, |mollifiedKernel ρ ε z| ≤ max BM 0 := by
    intro z
    exact (hMB z).trans (le_max_left BM 0)
  have hMtop : MemLp (mollifiedKernel ρ ε) ⊤ :=
    memLp_top_of_bound hMc.aestronglyMeasurable (max BM 0)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hMbound z)
  have hMone : MemLp (mollifiedKernel ρ ε) 1 := memLp_one_iff_integrable.mpr hMi
  have hwick : Integrable (fun z => mollifiedKernel ρ ε z ^ 2) := by
    have hmul := hMtop.integrable_mul hMone
    change Integrable ((fun z => mollifiedKernel ρ ε z) * mollifiedKernel ρ ε)
      (volume : Measure SpaceTime) at hmul
    change Integrable (fun z => mollifiedKernel ρ ε z ^ 2)
      (volume : Measure SpaceTime)
    exact hmul.congr (Filter.Eventually.of_forall fun z => by simp [pow_two])
  rcases covariance_facts ρ hρ hεpos with ⟨hQint, hQc, BQ, hQB⟩
  have hQbound : ∀ z, |covariance ρ ε z| ≤ max BQ 0 := by
    intro z
    exact (hQB z).trans (le_max_left BQ 0)
  have hQsqtop : MemLp (fun z => covariance ρ ε z ^ 2) ⊤ := by
    apply memLp_top_of_bound (hQc.measurable.pow_const 2).aestronglyMeasurable
      ((max BQ 0) ^ 2)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (covariance ρ ε z), hQbound z]
  have hsunset : Integrable fun z => massiveHeatKernel z * covariance ρ ε z ^ 2 := by
    have hmul := hQsqtop.integrable_mul
      (memLp_one_iff_integrable.mpr hG)
    change Integrable ((fun z => covariance ρ ε z ^ 2) * massiveHeatKernel)
      (volume : Measure SpaceTime) at hmul
    change Integrable (fun z => massiveHeatKernel z * covariance ρ ε z ^ 2)
      (volume : Measure SpaceTime)
    exact hmul.congr (Filter.Eventually.of_forall fun z => by simp [mul_comm])
  exact ⟨hG, hLp, hGconv, ⟨hMc, hMi, BM, hMB⟩, hQint,
    ⟨hQc, BQ, hQB⟩, hwick, hsunset⟩

end Phi43

end RegularityStructures

end
