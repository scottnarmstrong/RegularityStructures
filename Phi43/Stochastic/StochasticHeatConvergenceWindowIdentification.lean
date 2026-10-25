/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceShiftedModeBounds
public import Phi43.Stochastic.StochasticHeatConvergenceWindowDerivativeBounds
public import Phi43.RegularisedNoise.SmoothVersion.Approximation
public import Phi43.RegularisedNoise.SmoothVersion.WhiteNoiseLp

/-!
# Identification of a fixed-window Fourier series with white noise

Physical Fourier sums converge in `L²`; the white-noise covariance isometry
transfers this convergence to probability space. The already proved random
polynomial bound gives almost-sure absolute convergence. Uniqueness of limits
in measure identifies the series at every fixed observation point inside the
window. This is the local version-identification step for the global growth
proof of the convergence of the noise potentials (`phi43Noise_cauchy`) [Hai14, Proposition 9.5].
-/

public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.Phi43

private theorem fixed_window_mode_bound_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {a b : ℝ} (hab : a < b) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Sum WindowFrequency WindowFrequency,
      |W (smoothVersionWindowPhysicalMode a b i) ω| ≤
        C * smoothVersionFrequencyNormSq (i.elim id id) ^ 3 := by
  filter_upwards [whiteNoise_ae_shifted_modes_bound hW hab] with ω hω
  obtain ⟨C, hC, hbound⟩ := hω
  refine ⟨C, hC, fun i => ?_⟩
  have heq : stochasticHeatShiftedWindowMode a b 0 i = smoothVersionWindowPhysicalMode a b i := by
    funext w
    simp only [stochasticHeatShiftedWindowMode, Int.cast_zero, Prod.mk_zero_zero, sub_zero]
  simpa only [heq, stochasticHeatShiftedModeWeight, Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
    add_zero, one_mul] using hbound 0 i

theorem whiteNoise_fixedWindowSeries_eq_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ w : SpaceTime, R < |w.1| → Phi w = 0) (hR0 : 0 ≤ R)
    {a b : ℝ} (ha : a = -N - R - 1) (hb : b = N + R + 1)
    {z : SpaceTime} (hz : |z.1| < N) :
    (fun ω => ∑' i : Sum WindowFrequency WindowFrequency,
      smoothVersionWindowSeriesTerm Phi a b i z * W (smoothVersionWindowPhysicalMode a b i) ω) =ᵐ[P]
        W (fun w => Phi (z - w)) := by
  have hN : 0 < N := (abs_nonneg z.1).trans_lt hz
  have hab : a < b := by rw [ha, hb]; linarith only [hN, hR0]
  have hL : 1 ≤ b - a := by rw [ha, hb]; linarith only [hN, hR0]
  let e := smoothVersionWindowPhysicalMode a b
  let A := fun i => smoothVersionWindowSeriesTerm Phi a b i z
  have he : ∀ i, MemLp (e i) 2 := by
    intro i
    cases i with
    | inl k => exact memLp_windowFourierRealTestMode hab k
    | inr k => exact memLp_windowFourierImagTestMode hab k
  obtain ⟨s, hscover, hsmono, hK, hLp⟩ :=
    smoothVersion_windowPhysicalKernel_tendsto_Lp hPhi hR hR0 hz ha hb
  have hh := memLp_translate_of_isSmoothOnSpaceTime_of_timeSupport hPhi hR z
  have hK' : ∀ n, MemLp (∑ i ∈ s n, A i • e i) 2 := by
    intro n
    refine (memLp_congr_ae (μ := (volume : Measure SpaceTime)) ?_).2 (hK n)
    filter_upwards [] with w
    simp only [e, A, Finset.sum_apply, Pi.smul_apply]
  have hto (n : ℕ) :
      (hK' n).toLp (∑ i ∈ s n, A i • e i) =
        (hK n).toLp (fun w => ∑ i ∈ s n,
          smoothVersionWindowSeriesTerm Phi a b i z • smoothVersionWindowPhysicalMode a b i w) := by
    apply MemLp.toLp_congr
    filter_upwards [] with w
    simp only [e, A, Finset.sum_apply, Pi.smul_apply]
  have hLp' : Tendsto (fun n => (hK' n).toLp (∑ i ∈ s n, A i • e i)) atTop
      (𝓝 (hh.toLp (fun w => Phi (z - w)))) := by
    apply hLp.congr'
    exact Filter.Eventually.of_forall fun n => (hto n).symm
  have hpartial : ∀ n, MemLp (fun ω => ∑ i ∈ s n, A i * W (e i) ω) 2 P := by
    intro n
    apply memLp_finsetSum
    intro i _
    exact ((hW.2 1 (fun _ => e i) (fun _ => he i)).memLp_two_apply 0).const_mul _
  have hseries : ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ s n, A i * W (e i) ω) atTop
      (𝓝 (∑' i, A i * W (e i) ω)) := by
    filter_upwards [fixed_window_mode_bound_ae hW hab] with ω hω
    obtain ⟨C, hC, hbound⟩ := hω
    have hs := summable_stochasticHeatWindowSeries hPhi hR hR0 hN ha hb hL hC hbound z
    have hs' : Summable (fun i => A i * W (e i) ω) := by
      apply hs.congr
      intro i
      exact mul_comm _ _
    exact hs'.hasSum.comp (Filter.tendsto_atTop_finset_of_monotone hsmono hscover)
  exact whiteNoise_ae_eq_tsum_of_tendsto_Lp hW s A e
    ((hW.2 1 (fun _ => fun w => Phi (z - w)) (fun _ => hh)).memLp_two_apply 0)
    he hK' hpartial (tendsto_whiteNoise_toLp_of_tendsto_kernel_toLp hW hh hK' hLp') hseries

private theorem ae_eqOn_of_continuous {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → SpaceTime → ℝ} {U : Set SpaceTime}
    (hX : ∀ᵐ ω ∂P, Continuous (X ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y ω))
    (hpt : ∀ z ∈ U, (fun ω => X ω z) =ᵐ[P] fun ω => Y ω z) :
    ∀ᵐ ω ∂P, Set.EqOn (X ω) (Y ω) U := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense U
  let _ : Countable D := hDc.to_subtype
  have hD : ∀ᵐ ω ∂P, ∀ z : D, X ω z.1.1 = Y ω z.1.1 :=
    ae_all_iff.2 fun z => hpt z.1.1 z.1.2
  filter_upwards [hX, hY, hD] with ω hx hy hω
  have heq : (fun z : U => X ω z) = fun z : U => Y ω z :=
    hDd.denseRange_val.equalizer (hx.comp continuous_subtype_val)
      (hy.comp continuous_subtype_val) (funext hω)
  intro z hz
  exact congrFun heq ⟨z, hz⟩

theorem whiteNoise_fixedWindowSeries_eqOn_ae_of_mode_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ w : SpaceTime, R < |w.1| → Phi w = 0) (hR0 : 0 ≤ R) (hN : 0 < N)
    {a b : ℝ} (ha : a = -N - R - 1) (hb : b = N + R + 1)
    {ξ : Ω → SpaceTime → ℝ} (hξ : ∀ ω, IsSmoothOnSpaceTime (ξ ω))
    (hversion : ∀ z : SpaceTime, (fun ω => ξ ω z) =ᵐ[P] W (fun w => Phi (z - w)))
    (hmode : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : Sum WindowFrequency WindowFrequency,
        |W (smoothVersionWindowPhysicalMode a b i) ω| ≤
          C * smoothVersionFrequencyNormSq (i.elim id id) ^ 3) :
    ∀ᵐ ω ∂P, ∀ z : SpaceTime, |z.1| < N → ξ ω z =
      ∑' i : Sum WindowFrequency WindowFrequency,
        W (smoothVersionWindowPhysicalMode a b i) ω * smoothVersionWindowSeriesTerm Phi a b i z := by
  have hab : a < b := by rw [ha, hb]; linarith only [hN, hR0]
  have hL : 1 ≤ b - a := by rw [ha, hb]; linarith only [hN, hR0]
  apply ae_eqOn_of_continuous
    (Filter.Eventually.of_forall fun ω => Continuous.continuous_of_isSmoothOnSpaceTime (hξ ω))
    ?_ ?_
  · filter_upwards [hmode] with ω hω
    obtain ⟨C, hC, hbound⟩ := hω
    have hmatch : ∀ i : Sum WindowFrequency WindowFrequency,
        |W (smoothVersionWindowPhysicalMode a b i) ω| ≤ C *
          smoothVersionFrequencyNormSq (match i with | .inl k => k | .inr k => k) ^ 3 := by
      intro i
      cases i <;> exact hbound _
    exact Continuous.continuous_of_isSmoothOnSpaceTime
      (isSmoothOnSpaceTime_tsum_smoothVersionWindowSeries_of_polynomial_growth
        hPhi hR hR0 hN ha hb hL hC hmatch)
  · intro z hz
    filter_upwards [hversion z, whiteNoise_fixedWindowSeries_eq_ae hW hPhi hR hR0 ha hb hz]
      with ω hx hs
    exact hx.trans (hs.symm.trans (tsum_congr fun i => mul_comm _ _))

end RegularityStructures.Phi43

end
