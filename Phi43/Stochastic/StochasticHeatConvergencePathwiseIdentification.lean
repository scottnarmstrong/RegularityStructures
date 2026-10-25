/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePathwiseSecondMoment
public import Phi43.Stochastic.StationaryField
import Phi43.Stochastic.WhiteNoiseCovariance
public import Phi43.Stochastic.WhiteNoiseCovariance

/-!
# Identification of the pathwise and canonical stationary fields

For every jointly measurable regularised-noise version the pathwise massive heat convolution
agrees almost surely at each point with the canonical white-noise pairing. The proof computes
the mixed moment by Fubini and then shows the mean-square difference is zero. All stochastic
and deterministic integrability inputs are proved from the mollifier and white-noise premises.

Source: the statement, equation (2.2) and Definition 2.5.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem abs_product_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith only [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

theorem regularisedNoise_massiveHeatKernel_convolution_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    (fun ω => ∫ w : SpaceTime, massiveHeatKernel (z - w) * ξ ω w) =ᵐ[P]
      stationaryField W ρ ε z := by
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let φ : SpaceTime → ℝ := fun x => massiveHeatKernel (z - x)
  let k : SpaceTime → SpaceTime → ℝ := mollifierAt ρ ε
  let K : SpaceTime → ℝ := fun v => mollifiedKernel ρ ε (z - v)
  let A : Ω → ℝ := fun ω => ∫ x : SpaceTime, φ x * ξ ω x
  let B : Ω → ℝ := W K
  let I : ℝ := ∫ v : SpaceTime, K v ^ 2
  let V : ℝ := ∫ v : SpaceTime, periodise ρ ε v ^ 2
  have hφm : Measurable φ := measurable_massiveHeatKernel.comp (measurable_const.sub measurable_id)
  have hφi : Integrable φ := integrable_comp_sub_left_spaceTime integrable_massiveHeatKernel z
  obtain ⟨hGc, hGi, _⟩ := mollifiedKernel_facts ρ hρ hε
  have hGsq : Integrable (fun v : SpaceTime => mollifiedKernel ρ ε v ^ 2) := by
    simpa only [zero_add, pow_two] using (covariance_facts ρ hρ hε).1 0
  have hK : MemLp K 2 := by
    apply memLp_mollifiedKernel_sub
    exact (memLp_two_iff_integrable_sq hGc.aestronglyMeasurable).mpr hGsq
  have hKi : Integrable K := integrable_comp_sub_left_spaceTime hGi z
  have hKm : Measurable K := hGc.measurable.comp (measurable_const.sub measurable_id)
  have hA : MemLp A 2 P := regularisedNoise_massiveHeatKernel_memLp_two hW ρ hρ hε ξ hξ z
  have hB : MemLp B 2 P := (whiteNoise_pairing_hasGaussianLaw hW hK).memLp_two
  have hBm : Measurable B := hW.1 K hK
  have hAsq : (∫ ω, A ω ^ 2 ∂P) = I :=
    regularisedNoise_massiveHeatKernel_second_moment_eq hW ρ hρ hε ξ hξ z
  have hBsq : (∫ ω, B ω ^ 2 ∂P) = I := whiteNoise_pairing_sq_integral hW hK
  have hξm := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  have hξB (x : SpaceTime) : Integrable (fun ω => ξ ω x * B ω) P :=
    (regularisedNoise_memLp_two hW ρ hρ hε ξ hξ x).integrable_mul hB
  have hξBbound (x : SpaceTime) : (∫ ω, |ξ ω x * B ω| ∂P) ≤ (V + I) / 2 := by
    have hX := regularisedNoise_memLp_two hW ρ hρ hε ξ hξ x
    calc
      _ ≤ ∫ ω, (ξ ω x ^ 2 + B ω ^ 2) / 2 ∂P :=
        integral_mono (hξB x).norm ((hX.integrable_sq.add hB.integrable_sq).div_const 2)
          (fun ω => abs_product_le_half_sq _ _)
      _ = _ := by
        simp_rw [div_eq_mul_inv]
        rw [integral_mul_const, integral_add hX.integrable_sq hB.integrable_sq,
          regularisedNoise_second_moment_eq_periodise_sq hW ρ hρ hε ξ hξ x, hBsq]
  let J : SpaceTime × Ω → ℝ := fun q => φ q.1 * (ξ q.2 q.1 * B q.2)
  have hJm : Measurable J :=
    (hφm.comp measurable_fst).mul
      ((hξm.comp measurable_swap).mul (hBm.comp measurable_snd))
  have hJi : Integrable J ((volume : Measure SpaceTime).prod P) := by
    apply (integrable_prod_iff hJm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall fun x => (hξB x).const_mul (φ x), ?_⟩
    apply (hφi.norm.mul_const ((V + I) / 2)).mono'
      hJm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
    calc
      _ = ‖φ x‖ * ∫ ω, |ξ ω x * B ω| ∂P := by
        simp only [J, norm_mul, Real.norm_eq_abs, abs_mul]
        exact integral_const_mul _ _
      _ ≤ ‖φ x‖ * ((V + I) / 2) :=
        mul_le_mul_of_nonneg_left (hξBbound x) (norm_nonneg _)
  have hcross (x : SpaceTime) : (∫ ω, ξ ω x * B ω ∂P) = ∫ v : SpaceTime, k x v * K v := by
    calc
      _ = ∫ ω, W (k x) ω * W K ω ∂P := by
        apply integral_congr_ae
        filter_upwards [(hξ.2 x).2] with ω hω
        rw [hω]
      _ = _ := whiteNoise_pairing_mul_integral hW (memLp_mollifierAt ρ hρ hε x) hK
  obtain ⟨D, hD⟩ := bounded_periodise ρ hρ hε
  let F : SpaceTime × SpaceTime → ℝ := fun q => φ q.1 * k q.1 q.2 * K q.2
  have hFm : Measurable F :=
    ((hφm.comp measurable_fst).mul
      ((measurable_periodise ρ hρ).comp (measurable_fst.sub measurable_snd))).mul
      (hKm.comp measurable_snd)
  have hFi : Integrable F ((volume : Measure SpaceTime).prod volume) := by
    apply ((hφi.norm.mul_prod hKi.norm).const_mul D).mono' hFm.aestronglyMeasurable
    filter_upwards [] with q
    change ‖φ q.1 * k q.1 q.2 * K q.2‖ ≤ D * (‖φ q.1‖ * ‖K q.2‖)
    rw [norm_mul, norm_mul, Real.norm_eq_abs (k q.1 q.2)]
    calc
      _ ≤ (‖φ q.1‖ * D) * ‖K q.2‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hD (q.1 - q.2)) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hdet : (∫ x : SpaceTime, φ x * ∫ v : SpaceTime, k x v * K v) = I := by
    calc
      _ = ∫ x : SpaceTime, ∫ v : SpaceTime, F (x, v) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with v
        dsimp [F]
        ring
      _ = ∫ v : SpaceTime, ∫ x : SpaceTime, F (x, v) := integral_integral_swap hFi
      _ = I := by
        apply integral_congr_ae
        filter_upwards [] with v
        change (∫ x : SpaceTime, (φ x * k x v) * K v) = K v ^ 2
        rw [integral_mul_const]
        rw [integral_massiveHeatKernel_mul_mollifierAt_eq_mollifiedKernel ρ z v]
        exact (pow_two _).symm
  have hAB : (∫ ω, A ω * B ω ∂P) = I := by
    calc
      _ = ∫ ω, (∫ x : SpaceTime, J (x, ω)) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        change (∫ x : SpaceTime, φ x * ξ ω x) * B ω = ∫ x : SpaceTime, J (x, ω)
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [J]
        ring
      _ = ∫ x : SpaceTime, ∫ ω, J (x, ω) ∂P := integral_integral_swap hJi.swap
      _ = ∫ x : SpaceTime, φ x * ∫ v : SpaceTime, k x v * K v := by
        apply integral_congr_ae
        filter_upwards [] with x
        change (∫ ω, φ x * (ξ ω x * B ω) ∂P) = _
        rw [integral_const_mul, hcross]
      _ = I := hdet
  have hdiff : Integrable (fun ω => (A ω - B ω) ^ 2) P := (hA.sub hB).integrable_sq
  have hABi : Integrable (fun ω => A ω * B ω) P := hA.integrable_mul hB
  have hzero : (∫ ω, (A ω - B ω) ^ 2 ∂P) = 0 := by
    calc
      _ = ∫ ω, A ω ^ 2 + B ω ^ 2 - 2 * (A ω * B ω) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = 0 := by
        have hsum : Integrable (fun ω => A ω ^ 2 + B ω ^ 2) P :=
          hA.integrable_sq.add hB.integrable_sq
        rw [integral_sub hsum (hABi.const_mul 2),
          integral_add hA.integrable_sq hB.integrable_sq, integral_const_mul, hAsq, hBsq, hAB]
        ring
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => sq_nonneg (A ω - B ω)) hdiff).mp hzero
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

end RegularityStructures.Phi43

end
