/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.AnnealedNoiseBridge
public import Phi43.Stochastic.MollifierL1
public import RegularityStructures.Probability.GaussianMoments
public import RegularityStructures.Probability.GaussianVector

/-!
# Annealed moments of torus test-function pairings

The parabolic test class is lifted to `SpaceTime` by the Ioc fundamental-domain representative. The
white-noise covariance identity then gives the uniform second moment. Higher even moments use the
one-dimensional Gaussian law of each pairing; the normalization identity is the standard Gaussian
scaling formula corresponding to [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RegularityStructures

theorem whiteNoise_pairing_hasGaussianLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {g : SpaceTime → ℝ} (hg : MemLp g 2) :
    HasGaussianLaw (W g) P := by
  have hvec := hW.2 1 (fun _ : Fin 1 => g) (by
    intro i
    simpa using hg)
  simpa using hvec.hasGaussianLaw_apply 0

theorem whiteNoise_pairing_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {g : SpaceTime → ℝ} (hg : MemLp g 2) :
    ∫ ω, W g ω ∂P = 0 := by
  have hvec := hW.2 1 (fun _ : Fin 1 => g) (by
    intro i
    simpa using hg)
  exact hvec.integral_apply 0

theorem gaussian_even_abs_moment_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → ℝ} (hY : HasGaussianLaw Y P)
    (h0 : ∫ ω, Y ω ∂P = 0) (m : ℕ) :
    ∫ ω, |Y ω| ^ (2 * m) ∂P =
      (∫ x, |x| ^ (2 * m) ∂gaussianReal 0 1) * (Var[Y; P]) ^ m := by
  let v : ℝ := Var[Y; P]
  have hv : 0 ≤ v := by
    dsimp [v]
    exact variance_nonneg _ _
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) =
      gaussianReal 0 (Real.toNNReal v) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.eq
      simp [Real.sq_sqrt hv, hv]
  have hpow := hY.integral_pow_eq h0 (2 * m)
  have hpow_map :
      ∫ x, x ^ (2 * m) ∂gaussianReal 0 (Real.toNNReal v) =
        ∫ x, (Real.sqrt v * x) ^ (2 * m) ∂gaussianReal 0 1 := by
    rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have hpoint (x : ℝ) :
      (Real.sqrt v * x) ^ (2 * m) = v ^ m * x ^ (2 * m) := by
    rw [mul_pow, pow_mul, Real.sq_sqrt hv]
  have hpow_scale :
      ∫ x, x ^ (2 * m) ∂gaussianReal 0 (Real.toNNReal v) =
        v ^ m * ∫ x, x ^ (2 * m) ∂gaussianReal 0 1 := by
    rw [hpow_map]
    rw [show (fun x : ℝ => (Real.sqrt v * x) ^ (2 * m)) =
        fun x => v ^ m * x ^ (2 * m) by
      funext x
      exact hpoint x]
    rw [integral_const_mul]
  have habs :
      ∫ ω, |Y ω| ^ (2 * m) ∂P = ∫ ω, Y ω ^ (2 * m) ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact pow_abs_two_mul (Y ω)
  have hstd :
      ∫ x, x ^ (2 * m) ∂gaussianReal 0 1 =
        ∫ x, |x| ^ (2 * m) ∂gaussianReal 0 1 := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact (pow_abs_two_mul x).symm
  rw [habs, hpow, hpow_scale, hstd]
  dsimp [v]
  ring

end RegularityStructures

end
