/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WhiteNoise
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The white-noise `L²` distance identity

The covariance clause for an arbitrary white noise identifies the distance between two random
`L²` evaluations with the distance between their deterministic kernels.  This is the exact
isometry used to transfer finite Fourier partial sums from the window torus to the probability
space.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped ENNReal Topology

namespace RegularityStructures.Phi43

theorem whiteNoise_edist_toLp_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime))
    (hg : MemLp g 2 (volume : Measure SpaceTime)) :
    edist (((hW.2 1 (fun _ => h) (fun _ => hh)).memLp_two_apply 0).toLp
        (fun ω => W h ω))
        (((hW.2 1 (fun _ => g) (fun _ => hg)).memLp_two_apply 0).toLp
          (fun ω => W g ω)) =
      edist (hh.toLp h) (hg.toLp g) := by
  let hnoise := (hW.2 1 (fun _ => h) (fun _ => hh)).memLp_two_apply 0
  let gnoise := (hW.2 1 (fun _ => g) (fun _ => hg)).memLp_two_apply 0
  have hnoiseNorm := (hnoise.sub gnoise).eLpNorm_eq_integral_rpow_norm
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  have hkernelNorm := (hh.sub hg).eLpNorm_eq_integral_rpow_norm
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  rw [Lp.edist_toLp_toLp, Lp.edist_toLp_toLp]
  rw [hnoiseNorm, hkernelNorm]
  have hnorm_noise :
      (∫ ω, ‖W h ω - W g ω‖ ^ (2 : ℝ) ∂P) =
        ∫ ω, (W h ω - W g ω) ^ (2 : ℕ) ∂P := by
    congr 1
    funext ω
    simp [Real.norm_eq_abs, sq_abs]
  have hnorm_kernel :
      (∫ z, ‖h z - g z‖ ^ (2 : ℝ)) =
        ∫ z, (h z - g z) ^ (2 : ℕ) := by
    congr 1
    funext z
    simp [Real.norm_eq_abs, sq_abs]
  have hnorm_noise' :
      (∫ ω, ‖((fun ω => W h ω) - (fun ω => W g ω)) ω‖ ^
          ENNReal.toReal (2 : ℝ≥0∞) ∂P) =
        ∫ ω, (W h ω - W g ω) ^ (2 : ℕ) ∂P := by
    convert hnorm_noise using 1;
      simp [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  have hnorm_kernel' :
      (∫ z, ‖(h - g) z‖ ^ ENNReal.toReal (2 : ℝ≥0∞)) =
        ∫ z, (h z - g z) ^ (2 : ℕ) := by
    convert hnorm_kernel using 1;
      simp [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  rw [hnorm_noise', hnorm_kernel', whiteNoise_integral_sub_sq_eq hW hh hg]

theorem whiteNoise_dist_toLp_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime))
    (hg : MemLp g 2 (volume : Measure SpaceTime)) :
    dist (((hW.2 1 (fun _ => h) (fun _ => hh)).memLp_two_apply 0).toLp
        (fun ω => W h ω))
        (((hW.2 1 (fun _ => g) (fun _ => hg)).memLp_two_apply 0).toLp
          (fun ω => W g ω)) =
      dist (hh.toLp h) (hg.toLp g) := by
  have heq := whiteNoise_edist_toLp_eq hW hh hg
  have hreal := congrArg ENNReal.toReal heq
  have hdn : 0 ≤ dist
      (((hW.2 1 (fun _ => h) (fun _ => hh)).memLp_two_apply 0).toLp
        (fun ω => W h ω))
      (((hW.2 1 (fun _ => g) (fun _ => hg)).memLp_two_apply 0).toLp
        (fun ω => W g ω)) := dist_nonneg
  have hdk : 0 ≤ dist (hh.toLp h) (hg.toLp g) := dist_nonneg
  simpa [Lp.edist_dist, ENNReal.toReal_ofReal hdn,
    ENNReal.toReal_ofReal hdk] using hreal

theorem tendsto_whiteNoise_toLp_of_tendsto_kernel_toLp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime))
    {K : ℕ → SpaceTime → ℝ} (hK : ∀ n, MemLp (K n) 2 (volume : Measure SpaceTime))
    (hlim : Tendsto (fun n => (hK n).toLp (K n)) atTop
      (𝓝 (hh.toLp h))) :
    Tendsto
      (fun n =>
        ((hW.2 1 (fun _ => K n) (fun _ => hK n)).memLp_two_apply 0).toLp
          (fun ω => W (K n) ω)) atTop
      (𝓝 (((hW.2 1 (fun _ => h) (fun _ => hh)).memLp_two_apply 0).toLp
        (fun ω => W h ω))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist := hlim.dist
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => hh.toLp h) atTop (𝓝 (hh.toLp h)))
  have hdist0 : Tendsto
      (fun n => dist ((hK n).toLp (K n)) (hh.toLp h)) atTop (𝓝 0) := by
    simpa using hdist
  apply hdist0.congr'
  filter_upwards [] with n
  exact (whiteNoise_dist_toLp_eq hW (hK n) hh).symm

end RegularityStructures.Phi43

end
