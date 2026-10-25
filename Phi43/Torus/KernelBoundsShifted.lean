/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsLocal
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Integrable shifted parabolic majorants

These are elementary consequences of the homogeneous dimension-five volume estimate.  They
package the two estimates used in the covariance convolution: a globally integrable sixth-power
majorant, and a locally integrable regularised cubic majorant.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

namespace Phi43

def shiftedParabolicCube (e : ℝ) (z : SpaceTime) : ℝ :=
  (torusParabolicSize z + e) ^ (-(3 : ℝ))

def shiftedParabolicSix (e : ℝ) (z : SpaceTime) : ℝ :=
  (torusParabolicSize z + e) ^ (-(6 : ℝ))

theorem measurable_shiftedParabolicCube {e : ℝ} (he : 0 < e) :
    Measurable (shiftedParabolicCube e) := by
  have hp := (measurable_pos_rpow_extension (-(3 : ℝ))).comp
    (measurable_torusParabolicSize.add (measurable_const : Measurable (fun _ : SpaceTime => e)))
  convert hp using 1
  funext z
  have hz : 0 < torusParabolicSize z + e :=
    lt_of_lt_of_le he (by linarith [torusParabolicSize_nonneg z])
  simp [shiftedParabolicCube, hz]

theorem measurable_shiftedParabolicSix {e : ℝ} (he : 0 < e) :
    Measurable (shiftedParabolicSix e) := by
  have hp := (measurable_pos_rpow_extension (-(6 : ℝ))).comp
    (measurable_torusParabolicSize.add (measurable_const : Measurable (fun _ : SpaceTime => e)))
  convert hp using 1
  funext z
  have hz : 0 < torusParabolicSize z + e :=
    lt_of_lt_of_le he (by linarith [torusParabolicSize_nonneg z])
  simp [shiftedParabolicSix, hz]

theorem shiftedParabolicCube_nonneg {e : ℝ} (he : 0 < e) (z : SpaceTime) :
    0 ≤ shiftedParabolicCube e z := by
  unfold shiftedParabolicCube
  exact Real.rpow_nonneg (add_nonneg (torusParabolicSize_nonneg z) he.le) _

theorem shiftedParabolicSix_nonneg {e : ℝ} (he : 0 < e) (z : SpaceTime) :
    0 ≤ shiftedParabolicSix e z := by
  unfold shiftedParabolicSix
  exact Real.rpow_nonneg (add_nonneg (torusParabolicSize_nonneg z) he.le) _

theorem integrable_truncatedParabolicWeight {e : ℝ} (he : 0 < e) :
    Integrable (truncatedParabolicWeight e) := by
  have hf := measurable_truncatedParabolicWeight he
  have hnn : 0 ≤ᵐ[volume] truncatedParabolicWeight e :=
    Filter.Eventually.of_forall (truncatedParabolicWeight_nonneg (r := e))
  apply (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp
  exact ne_of_lt ((lintegral_truncatedParabolicWeight_le he).trans_lt
    ENNReal.ofReal_lt_top)

theorem integral_truncatedParabolicWeight_le {e : ℝ} (he : 0 < e) :
    ∫ z : SpaceTime, truncatedParabolicWeight e z ≤ 96 / e := by
  have htail := integrable_truncatedParabolicWeight he
  have hE := lintegral_truncatedParabolicWeight_le he
  have hEq := ofReal_integral_eq_lintegral_ofReal htail
    (Filter.Eventually.of_forall (truncatedParabolicWeight_nonneg (r := e)))
  have hle : ENNReal.ofReal (∫ z, truncatedParabolicWeight e z) ≤
      ENNReal.ofReal (96 / e) := hEq.symm ▸ hE
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle

private theorem integrable_ball_const {e : ℝ} (he : 0 < e) :
    Integrable ({z : SpaceTime | torusParabolicSize z ≤ e}.indicator
      (fun _ : SpaceTime => e ^ (-(6 : ℝ)))) := by
  let S : Set SpaceTime := {z : SpaceTime | torusParabolicSize z ≤ e}
  have hS : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
  have hvol : volume S < ⊤ := by
    apply lt_of_le_of_lt (volume_torusParabolicBall_le_global he.le)
    exact ENNReal.ofReal_lt_top
  exact (integrableOn_const hvol.ne).integrable_indicator hS

private theorem integral_ball_const_le {e : ℝ} (he : 0 < e) :
    ∫ z : SpaceTime, (({z : SpaceTime | torusParabolicSize z ≤ e}).indicator
      (fun _ : SpaceTime => e ^ (-(6 : ℝ)))) z ≤ 16 / e := by
  let S : Set SpaceTime := {z : SpaceTime | torusParabolicSize z ≤ e}
  have hS : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
  have hvol : volume S ≤ ENNReal.ofReal (16 * e ^ 5) :=
    volume_torusParabolicBall_le_global he.le
  have hvol' : volume.real S ≤ 16 * e ^ 5 := by
    calc
      volume.real S ≤ (ENNReal.ofReal (16 * e ^ 5)).toReal := by
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
      _ = 16 * e ^ 5 := ENNReal.toReal_ofReal (by positivity)
  rw [integral_indicator_const _ hS, smul_eq_mul]
  calc
    volume.real S * e ^ (-(6 : ℝ)) ≤
        (16 * e ^ 5) * e ^ (-(6 : ℝ)) :=
      mul_le_mul_of_nonneg_right hvol' (Real.rpow_nonneg (le_of_lt he) _)
    _ = 16 / e := by
      calc
        (16 * e ^ 5) * e ^ (-(6 : ℝ)) = 16 / e := by
          norm_num [Real.rpow_neg]
          field_simp

theorem integrable_shiftedParabolicSix {e : ℝ} (he : 0 < e) :
    Integrable (shiftedParabolicSix e) := by
  have hball := integrable_ball_const he
  have htail := integrable_truncatedParabolicWeight he
  have hsum : Integrable
      (({z : SpaceTime | torusParabolicSize z ≤ e}).indicator
        (fun _ : SpaceTime => e ^ (-(6 : ℝ))) + truncatedParabolicWeight e) :=
    hball.add htail
  apply hsum.mono' (measurable_shiftedParabolicSix he).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  by_cases hz : torusParabolicSize z ≤ e
  · have hz' : z ∈ {z : SpaceTime | torusParabolicSize z ≤ e} := hz
    rw [Set.indicator_of_mem hz', abs_of_nonneg (shiftedParabolicSix_nonneg he z)]
    have hpow : (torusParabolicSize z + e) ^ (-(6 : ℝ)) ≤ e ^ (-(6 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos he (by linarith [torusParabolicSize_nonneg z]) (by norm_num)
    simp only [truncatedParabolicWeight, not_lt.mpr hz, ite_false, add_zero]
    exact hpow
  · have hz' : z ∉ {z : SpaceTime | torusParabolicSize z ≤ e} := hz
    rw [Set.indicator_of_notMem hz', abs_of_nonneg (shiftedParabolicSix_nonneg he z)]
    have hsz : e < torusParabolicSize z := lt_of_not_ge hz
    have hpow : (torusParabolicSize z + e) ^ (-(6 : ℝ)) ≤
        torusParabolicSize z ^ (-(6 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (lt_trans he hsz)
        (show torusParabolicSize z ≤ torusParabolicSize z + e by linarith)
        (by norm_num)
    simp only [truncatedParabolicWeight, hsz, ite_true, zero_add]
    exact hpow

theorem integral_shiftedParabolicSix_le {e : ℝ} (he : 0 < e) :
    ∫ z : SpaceTime, shiftedParabolicSix e z ≤ 112 / e := by
  have hf := integrable_shiftedParabolicSix he
  have hball := integrable_ball_const he
  have htail := integrable_truncatedParabolicWeight he
  have hpoint : ∀ z : SpaceTime,
      shiftedParabolicSix e z ≤
        (({z : SpaceTime | torusParabolicSize z ≤ e}).indicator
          (fun _ : SpaceTime => e ^ (-(6 : ℝ)))) z + truncatedParabolicWeight e z := by
    intro z
    by_cases hz : torusParabolicSize z ≤ e
    · have hz' : z ∈ {z : SpaceTime | torusParabolicSize z ≤ e} := hz
      rw [Set.indicator_of_mem hz']
      have hpow : (torusParabolicSize z + e) ^ (-(6 : ℝ)) ≤ e ^ (-(6 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos he
          (by linarith [torusParabolicSize_nonneg z]) (by norm_num : -(6 : ℝ) ≤ 0)
      simp only [truncatedParabolicWeight, not_lt.mpr hz, ite_false, add_zero]
      exact hpow
    · have hz' : z ∉ {z : SpaceTime | torusParabolicSize z ≤ e} := hz
      rw [Set.indicator_of_notMem hz']
      have hsz : e < torusParabolicSize z := lt_of_not_ge hz
      have hpow : (torusParabolicSize z + e) ^ (-(6 : ℝ)) ≤
          torusParabolicSize z ^ (-(6 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (lt_trans he hsz)
          (show torusParabolicSize z ≤ torusParabolicSize z + e by linarith)
          (by norm_num : -(6 : ℝ) ≤ 0)
      simp only [truncatedParabolicWeight, hsz, ite_true, zero_add]
      exact hpow
  calc
    ∫ z, shiftedParabolicSix e z ≤
        ∫ z, (({z : SpaceTime | torusParabolicSize z ≤ e}).indicator
          (fun _ : SpaceTime => e ^ (-(6 : ℝ))) + truncatedParabolicWeight e) z := by
      exact integral_mono hf (hball.add htail) hpoint
    _ = (∫ z, (({z : SpaceTime | torusParabolicSize z ≤ e}).indicator
          (fun _ : SpaceTime => e ^ (-(6 : ℝ)))) z) +
          ∫ z, truncatedParabolicWeight e z := by
      simpa only [Pi.add_apply] using (integral_add hball htail)
    _ ≤ 16 / e + 96 / e := by
      exact add_le_add (integral_ball_const_le he) (by
        have hE := lintegral_truncatedParabolicWeight_le he
        have hEq := ofReal_integral_eq_lintegral_ofReal htail
          (Filter.Eventually.of_forall (truncatedParabolicWeight_nonneg (r := e)))
        have hle : ENNReal.ofReal (∫ z, truncatedParabolicWeight e z) ≤
            ENNReal.ofReal (96 / e) := hEq.symm ▸ hE
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle)
    _ = 112 / e := by ring

theorem integrable_shiftedParabolicCube_on {e a : ℝ} (he : 0 < e) (ha : 0 < a) :
    Integrable ({z : SpaceTime | torusParabolicSize z ≤ a}.indicator
      (shiftedParabolicCube e)) := by
  let b : ℝ := min e a
  have hb : 0 < b := lt_min he ha
  let S : Set SpaceTime := {z : SpaceTime | torusParabolicSize z ≤ b}
  have hS : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
  have hball : Integrable (S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ)))) := by
    have hvol : volume S < ⊤ := by
      apply lt_of_le_of_lt (volume_torusParabolicBall_le_global hb.le)
      exact ENNReal.ofReal_lt_top
    exact (integrableOn_const hvol.ne).integrable_indicator hS
  have htail : Integrable (localParabolicWeight e a) := by
    have hf := measurable_localParabolicWeight (e := e) (a := a) he
    have hnn : 0 ≤ᵐ[volume] localParabolicWeight e a :=
      Filter.Eventually.of_forall (localParabolicWeight_nonneg (e := e) (a := a))
    apply (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp
    exact ne_of_lt ((integral_localParabolicWeight_le he ha).trans_lt ENNReal.ofReal_lt_top)
  have hsum : Integrable
      (S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ))) +
        localParabolicWeight e a) := hball.add htail
  have hA : MeasurableSet {z : SpaceTime | torusParabolicSize z ≤ a} :=
    measurableSet_le measurable_torusParabolicSize measurable_const
  apply hsum.mono' ((measurable_shiftedParabolicCube he).indicator hA).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  by_cases hza : torusParabolicSize z ≤ a
  · by_cases hzb : torusParabolicSize z ≤ b
    · have hza' : z ∈ {z : SpaceTime | torusParabolicSize z ≤ a} := hza
      have hzb' : z ∈ S := hzb
      rw [Set.indicator_of_mem hza', Set.indicator_of_mem hzb',
        abs_of_nonneg (shiftedParabolicCube_nonneg he z)]
      have hpow : (torusParabolicSize z + e) ^ (-(3 : ℝ)) ≤ e ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos he
          (by linarith [torusParabolicSize_nonneg z]) (by norm_num : -(3 : ℝ) ≤ 0)
      have hne : ¬ e < torusParabolicSize z := by
        exact not_lt_of_ge (le_trans hzb (by dsimp [b]; exact min_le_left _ _))
      simp [localParabolicWeight, hne]
      simpa [shiftedParabolicCube, Real.rpow_neg] using hpow
    · have hza' : z ∈ {z : SpaceTime | torusParabolicSize z ≤ a} := hza
      have hzb' : z ∉ S := hzb
      rw [Set.indicator_of_mem hza', Set.indicator_of_notMem hzb',
        abs_of_nonneg (shiftedParabolicCube_nonneg he z)]
      have hze : e < torusParabolicSize z := by
        by_contra h
        exact hzb (by
          dsimp [b]
          exact le_min (le_of_not_gt h) hza)
      simp [localParabolicWeight, hze, hza]
      have hpow : (torusParabolicSize z + e) ^ (-(3 : ℝ)) ≤
          torusParabolicSize z ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (lt_trans he hze)
          (show torusParabolicSize z ≤ torusParabolicSize z + e by linarith)
          (by norm_num : -(3 : ℝ) ≤ 0)
      simpa [shiftedParabolicCube, Real.rpow_neg] using hpow
  · have hza' : z ∉ {z : SpaceTime | torusParabolicSize z ≤ a} := hza
    rw [Set.indicator_of_notMem hza']
    simp only [abs_zero]
    have hball_nonneg : 0 ≤ S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ))) z := by
      by_cases hz : z ∈ S
      · simp [hz]
        positivity
      · simp [hz]
    exact add_nonneg hball_nonneg (localParabolicWeight_nonneg (e := e) (a := a) z)

theorem integral_shiftedParabolicCube_on_le {e a : ℝ} (he : 0 < e) (ha : 0 < a) :
    ∫ z : SpaceTime, (({z : SpaceTime | torusParabolicSize z ≤ a}).indicator
      (shiftedParabolicCube e)) z ≤ 56 * a ^ 2 := by
  let b : ℝ := min e a
  have hb : 0 < b := lt_min he ha
  let S : Set SpaceTime := {z : SpaceTime | torusParabolicSize z ≤ b}
  have hS : MeasurableSet S := measurableSet_le measurable_torusParabolicSize measurable_const
  have hball : Integrable (S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ)))) := by
    have hvol : volume S < ⊤ := by
      apply lt_of_le_of_lt (volume_torusParabolicBall_le_global hb.le)
      exact ENNReal.ofReal_lt_top
    exact (integrableOn_const hvol.ne).integrable_indicator hS
  have htail : Integrable (localParabolicWeight e a) := by
    have hf := measurable_localParabolicWeight (e := e) (a := a) he
    have hnn : 0 ≤ᵐ[volume] localParabolicWeight e a :=
      Filter.Eventually.of_forall (localParabolicWeight_nonneg (e := e) (a := a))
    apply (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp
    exact ne_of_lt ((integral_localParabolicWeight_le he ha).trans_lt ENNReal.ofReal_lt_top)
  have hleft := integrable_shiftedParabolicCube_on he ha
  have hpoint : ∀ z : SpaceTime,
      ({z : SpaceTime | torusParabolicSize z ≤ a}.indicator
        (shiftedParabolicCube e) z) ≤
        S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ))) z +
          localParabolicWeight e a z := by
    intro z
    by_cases hza : torusParabolicSize z ≤ a
    · by_cases hzb : torusParabolicSize z ≤ b
      · have hza' : z ∈ {z : SpaceTime | torusParabolicSize z ≤ a} := hza
        have hzb' : z ∈ S := hzb
        rw [Set.indicator_of_mem hza', Set.indicator_of_mem hzb']
        have hpow : (torusParabolicSize z + e) ^ (-(3 : ℝ)) ≤ e ^ (-(3 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos he
            (by linarith [torusParabolicSize_nonneg z]) (by norm_num : -(3 : ℝ) ≤ 0)
        have hne : ¬ e < torusParabolicSize z := by
          exact not_lt_of_ge (le_trans hzb (by dsimp [b]; exact min_le_left _ _))
        simp [localParabolicWeight, hne]
        simpa [shiftedParabolicCube, Real.rpow_neg] using hpow
      · have hza' : z ∈ {z : SpaceTime | torusParabolicSize z ≤ a} := hza
        have hzb' : z ∉ S := hzb
        rw [Set.indicator_of_mem hza', Set.indicator_of_notMem hzb']
        have hze : e < torusParabolicSize z := by
          by_contra h
          exact hzb (by
            dsimp [b]
            exact le_min (le_of_not_gt h) hza)
        simp [localParabolicWeight, hze, hza]
        have hpow : (torusParabolicSize z + e) ^ (-(3 : ℝ)) ≤
            torusParabolicSize z ^ (-(3 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (lt_trans he hze)
            (show torusParabolicSize z ≤ torusParabolicSize z + e by linarith)
            (by norm_num : -(3 : ℝ) ≤ 0)
        simpa [shiftedParabolicCube, Real.rpow_neg] using hpow
    · have hza' : z ∉ {z : SpaceTime | torusParabolicSize z ≤ a} := hza
      rw [Set.indicator_of_notMem hza']
      have hball_nonneg : 0 ≤ S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ))) z := by
        by_cases hz : z ∈ S
        · simp [hz]
          positivity
        · simp [hz]
      exact add_nonneg hball_nonneg
        (localParabolicWeight_nonneg (e := e) (a := a) z)
  have hsum : Integrable (S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ))) +
      localParabolicWeight e a) := hball.add htail
  have hbound : ∫ z, S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ))) z ≤ 16 * a ^ 2 := by
    have hvol : volume S ≤ ENNReal.ofReal (16 * b ^ 5) :=
      volume_torusParabolicBall_le_global hb.le
    have hvol' : volume.real S ≤ 16 * b ^ 5 := by
      calc
        volume.real S ≤ (ENNReal.ofReal (16 * b ^ 5)).toReal := by
          exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
        _ = 16 * b ^ 5 := ENNReal.toReal_ofReal (by positivity)
    rw [integral_indicator_const _ hS, smul_eq_mul]
    calc
      volume.real S * e ^ (-(3 : ℝ)) ≤
          (16 * b ^ 5) * e ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hvol' (Real.rpow_nonneg (le_of_lt he) _)
      _ ≤ 16 * a ^ 2 := by
        have hba : b ≤ a := min_le_right e a
        have hbe : b ≤ e := min_le_left e a
        have hb0 : 0 ≤ b := hb.le
        have hpow : b ^ 5 ≤ a ^ 2 * e ^ 3 := by
          calc
            b ^ 5 = b ^ 2 * b ^ 3 := by ring
            _ ≤ a ^ 2 * e ^ 3 := by
              gcongr
        calc
          (16 * b ^ 5) * e ^ (-(3 : ℝ)) ≤
              (16 * (a ^ 2 * e ^ 3)) * e ^ (-(3 : ℝ)) := by
                gcongr
          _ = 16 * a ^ 2 := by
            norm_num [Real.rpow_neg]
            field_simp
  calc
    ∫ z, ({z : SpaceTime | torusParabolicSize z ≤ a}.indicator
        (shiftedParabolicCube e) z) ≤
        ∫ z, (S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ))) +
          localParabolicWeight e a) z := by
      exact integral_mono hleft hsum hpoint
    _ = (∫ z, S.indicator (fun _ : SpaceTime => e ^ (-(3 : ℝ))) z) +
          ∫ z, localParabolicWeight e a z := by
      simpa only [Pi.add_apply] using (integral_add hball htail)
    _ ≤ 16 * a ^ 2 + 40 * a ^ 2 := by
      exact add_le_add hbound (by
        have hE := integral_localParabolicWeight_le he ha
        have hEq := ofReal_integral_eq_lintegral_ofReal htail
          (Filter.Eventually.of_forall (localParabolicWeight_nonneg (e := e) (a := a)))
        have hle : ENNReal.ofReal (∫ z, localParabolicWeight e a z) ≤
            ENNReal.ofReal (40 * a ^ 2) := hEq.symm ▸ hE
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle)
    _ = 56 * a ^ 2 := by ring

end Phi43

end RegularityStructures

end
