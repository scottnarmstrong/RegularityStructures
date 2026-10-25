/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceVersionFubini
public import Phi43.Stochastic.StochasticHeatConvergenceKernelL2
import Phi43.Stochastic.WhiteNoiseCovariance
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Phi43.Stochastic.StochasticHeatConvergenceMoments
public import RegularityStructures.Torus.KolmogorovHolderBesovHeat
public import Phi43.Stochastic.WhiteNoiseCovariance

/-!
# Heat-semigroup evaluations of continuous stationary-field versions

A measurable continuous spatial version has the same heat averages as the canonical
heat-regularised white-noise kernel. Center the random field and its deterministic kernels
at the candidate white-noise pairing. Covariance Fubini identifies the variance of the
centered heat average with zero; all integrability conditions follow from L² bounds.

Source: the statement, equation (2.1), and the stationary field following Definition 2.5.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem sub_sq_bound (a b : ℝ) : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith only [sq_nonneg (a + b)]

theorem heatSemigroup_stationaryField_version_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {t : ℝ} {X : Ω → C(Torus3, ℝ)} (hXm : Measurable X)
    (hX : ∀ y : Torus3, (fun ω => X ω y) =ᵐ[P] stationaryField W ρ ε (t, y))
    {s : ℝ} (hs : 0 < s) (x : Torus3) :
    (fun ω => heatSemigroup s (X ω) x) =ᵐ[P] stochasticHeatField W ρ ε s (t, x) := by
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let φ := heatKernel s
  let f : Torus3 → SpaceTime → ℝ := fun y v => mollifiedKernel ρ ε ((t, x - y) - v)
  let K := stochasticHeatKernel ρ ε s (t, x)
  let r : Torus3 → SpaceTime → ℝ := fun y => f y - K
  let R : Torus3 → Ω → ℝ := fun y ω => X ω (x - y) - W K ω
  let V : ℝ := ∫ v : SpaceTime, mollifiedKernel ρ ε v ^ 2
  let I : ℝ := ∫ v : SpaceTime, K v ^ 2
  let C := 2 * (V + I)
  obtain ⟨hGc, _, D, hD⟩ := mollifiedKernel_facts ρ hρ hε
  have hGsq : Integrable (fun v : SpaceTime => mollifiedKernel ρ ε v ^ 2) := by
    simpa only [zero_add, pow_two] using (covariance_facts ρ hρ hε).1 0
  have hG2 := (memLp_two_iff_integrable_sq hGc.aestronglyMeasurable).mpr hGsq
  have hf (y : Torus3) : MemLp (f y) 2 := memLp_mollifiedKernel_sub hG2 (t, x - y)
  have hK : MemLp K 2 := memLp_stochasticHeatKernel_of_integrable_square ρ hρ hε hs (t, x)
    (integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts ρ hρ hε hs (t, x))
  have hfm : Measurable (fun q : Torus3 × SpaceTime => f q.1 q.2) := by
    apply hGc.measurable.comp
    exact (measurable_const.prodMk (measurable_const.sub measurable_fst)).sub measurable_snd
  have hKm : Measurable K := (continuous_stochasticHeatKernel ρ hρ hε hs (t, x)).measurable
  have hrm : Measurable (fun q : Torus3 × SpaceTime => r q.1 q.2) :=
    hfm.sub (hKm.comp measurable_snd)
  have hr2 (y : Torus3) : MemLp (r y) 2 := (hf y).sub hK
  have hfsq (y : Torus3) : (∫ v : SpaceTime, f y v ^ 2) = V :=
    integral_comp_sub_left_spaceTime (fun v => mollifiedKernel ρ ε v ^ 2) (t, x - y)
  have hrbound (y : Torus3) : (∫ v : SpaceTime, r y v ^ 2) ≤ C := by
    calc
      _ ≤ ∫ v : SpaceTime, 2 * (f y v ^ 2 + K v ^ 2) :=
        integral_mono (hr2 y).integrable_sq
          (((hf y).integrable_sq.add hK.integrable_sq).const_mul 2) (fun v => sub_sq_bound _ _)
      _ = C := by rw [integral_const_mul, integral_add (hf y).integrable_sq hK.integrable_sq, hfsq]
  have hRpoint (y : Torus3) : R y =ᵐ[P] W (r y) := by
    filter_upwards [hX (x - y), whiteNoise_pairing_sub_ae hW (hf y) hK] with ω hω hsub
    change X ω (x - y) - W K ω = W (f y - K) ω
    change X ω (x - y) = W (f y) ω at hω
    rw [hω]
    exact hsub
  have hR2 (y : Torus3) : MemLp (R y) 2 P :=
    (memLp_congr_ae (hRpoint y)).mpr (whiteNoise_pairing_hasGaussianLaw hW (hr2 y)).memLp_two
  have hRm : Measurable (fun q : Torus3 × Ω => R q.1 q.2) := by
    have heval : Measurable (fun q : C(Torus3, ℝ) × Torus3 => q.1 q.2) :=
      continuous_eval.measurable
    exact (heval.comp ((hXm.comp measurable_snd).prodMk (measurable_const.sub measurable_fst))).sub
      ((hW.1 K hK).comp measurable_snd)
  have hRbound (y : Torus3) : (∫ ω, R y ω ^ 2 ∂P) ≤ C := by
    calc
      _ = ∫ ω, W (r y) ω ^ 2 ∂P := integral_congr_ae ((hRpoint y).fun_comp (fun a => a ^ 2))
      _ = ∫ v : SpaceTime, r y v ^ 2 := whiteNoise_pairing_sq_integral hW (hr2 y)
      _ ≤ C := hrbound y
  have hφm : Measurable φ := (continuous_heatKernel_fixed hs).measurable
  have hφi : Integrable φ := integrable_heatKernel_fixed hs
  have hRp := integrable_weighted_covariance_product_of_second_moment_bound hRm hR2 hRbound hφm hφi
  have hrp := integrable_weighted_covariance_product_of_second_moment_bound hrm hr2 hrbound hφm hφi
  have hRprod : Integrable (fun q : (Torus3 × Torus3) × Ω =>
      (φ q.1.1 * R q.1.1 q.2) * (φ q.1.2 * R q.1.2 q.2))
      (((volume : Measure Torus3).prod volume).prod P) := by
    apply hRp.congr
    filter_upwards [] with q
    ring
  have hrprod : Integrable (fun q : (Torus3 × Torus3) × SpaceTime =>
      (φ q.1.1 * r q.1.1 q.2) * (φ q.1.2 * r q.1.2 q.2))
      (((volume : Measure Torus3).prod volume).prod volume) := by
    apply hrp.congr
    filter_upwards [] with q
    ring
  have hcov (y y' : Torus3) :
      (∫ ω, (φ y * R y ω) * (φ y' * R y' ω) ∂P) =
        ∫ v : SpaceTime, (φ y * r y v) * (φ y' * r y' v) := by
    calc
      _ = (φ y * φ y') * ∫ ω, R y ω * R y' ω ∂P := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = (φ y * φ y') * ∫ v : SpaceTime, r y v * r y' v := by
        congr 1
        calc
          _ = ∫ ω, W (r y) ω * W (r y') ω ∂P := by
            apply integral_congr_ae
            filter_upwards [hRpoint y, hRpoint y'] with ω hω hω'
            rw [hω, hω']
          _ = _ := whiteNoise_pairing_mul_integral hW (hr2 y) (hr2 y')
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with v
        ring
  have hmean (v : SpaceTime) : (∫ y : Torus3, φ y * r y v) = 0 := by
    have hfi : Integrable (fun y : Torus3 => φ y * f y v) :=
      hφi.mul_bdd (hfm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hD _)
    have he : (fun y : Torus3 => φ y * r y v) = fun y => φ y * f y v - φ y * K v := by
      funext y
      change φ y * (f y v - K v) = _
      ring
    rw [he, integral_sub hfi (hφi.mul_const (K v)), integral_mul_const, integral_heatKernel hs]
    change K v - 1 * K v = 0
    ring
  have hzero : (∫ ω, (∫ y : Torus3, φ y * R y ω) ^ 2 ∂P) = 0 := by
    rw [integral_average_sq_eq_of_covariance hRprod hrprod hcov]
    simp only [hmean, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero]
  have hint : Integrable (fun ω => (∫ y : Torus3, φ y * R y ω) ^ 2) P := by
    apply hRprod.integral_prod_right.congr
    filter_upwards [] with ω
    exact (show (∫ q : Torus3 × Torus3, (φ q.1 * R q.1 ω) * (φ q.2 * R q.2 ω)
      ∂((volume : Measure Torus3).prod volume)) = (∫ y : Torus3, φ y * R y ω) ^ 2 from by
        rw [pow_two]
        exact integral_prod_mul (μ := (volume : Measure Torus3)) (ν := volume)
          (fun y => φ y * R y ω) (fun y => φ y * R y ω))
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => sq_nonneg (∫ y : Torus3, φ y * R y ω)) hint).mp hzero
  filter_upwards [hae] with ω hω
  have heq : (∫ y : Torus3, φ y * R y ω) = heatSemigroup s (X ω) x - W K ω := by
    rw [heatSemigroup_eq_torus_integral hs]
    have he : (fun y : Torus3 => φ y * R y ω) =
        fun y => φ y * X ω (x - y) - φ y * W K ω := by
      funext y
      dsimp [R]
      ring
    have hyi : Integrable (fun y : Torus3 => φ y * X ω (x - y)) :=
      ((continuous_heatKernel_fixed hs).mul ((X ω).continuous.comp
        (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [he, integral_sub hyi (hφi.mul_const (W K ω)), integral_mul_const, integral_heatKernel hs,
      one_mul]
  exact sub_eq_zero.mp (heq.symm.trans (sq_eq_zero_iff.mp hω))

end RegularityStructures.Phi43

end
