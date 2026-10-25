/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierWindowRate
public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierWindowSize
public import Phi43.Stochastic.StochasticHeatConvergencePathSpace
public import Mathlib.Order.CompletePartialOrder
public import Phi43.Stochastic.StochasticHeatConvergenceContinuousVersion
public import Phi43.Stochastic.StochasticHeatConvergencePathwiseIdentification

/-!
# Window estimates for arbitrary massive-potential representatives

An all-point potential identity identifies the supplied representative with a measurable continuous
version outside one null set. Consequently neither its measurability nor its continuity is an
additional hypothesis. The suprema below are exactly the bodies of the noise size `phi43NoiseSize`
and the noise distance on `[-1,T+1]`. This proves the moment and measurability components of the
convergence of the noise potentials (`phi43Noise_cauchy`), [Hai14, Proposition 9.5, (9.15)],
including two distinct mollifiers.
-/

public noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace RegularityStructures.Phi43

private theorem window_iSup_eq (T : ℝ) (hT : 1 ≤ T) (F : ℝ → ℝ≥0∞) :
    (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1), F t) =
      ⨆ u : UnitInterval, F ((T + 2) * u - 1) := by
  have hL : 0 < T + 2 := by linarith only [hT]
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    let u : UnitInterval := ⟨(t + 1) / (T + 2),
      (div_nonneg (by linarith only [ht.1]) hL.le),
      (div_le_one hL).mpr (by linarith only [ht.2])⟩
    have he : (T + 2) * (u : ℝ) - 1 = t := by
      dsimp [u]
      rw [mul_div_cancel₀ _ hL.ne']
      ring
    exact he ▸ le_iSup (fun v : UnitInterval => F ((T + 2) * v - 1)) u
  · refine iSup_le fun u => le_iSup₂_of_le ((T + 2) * u - 1) ?_ le_rfl
    constructor
    · have h := mul_nonneg hL.le u.property.1
      linarith only [h]
    · have h := mul_le_mul_of_nonneg_left u.property.2 hL.le
      linarith only [h]

private def windowPath (η : NegExponent) (T : ℝ) (f : C(ℝ, C(Torus3, ℝ))) :
    C(UnitInterval, HolderBesov η) :=
  stochasticHeatBesovPath η (T + 2)
    (f.comp ⟨fun t : ℝ => t - 1, continuous_id.sub continuous_const⟩)

private theorem continuous_windowPath (η : NegExponent) (T : ℝ) :
    Continuous (windowPath η T) :=
  (continuous_stochasticHeatBesovPath η (T + 2)).comp
    (ContinuousMap.continuous_precomp
      ⟨fun t : ℝ => t - 1, continuous_id.sub continuous_const⟩)

private theorem window_size_eq_enorm (η : NegExponent) (T : ℝ) (hT : 1 ≤ T)
    (f : C(ℝ, C(Torus3, ℝ))) :
    (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1), holderBesovENorm η (f t)) =
      ‖windowPath η T f‖ₑ := by
  rw [window_iSup_eq T hT, windowPath, enorm_stochasticHeatBesovPath]
  rfl

private theorem window_dist_eq_enorm (η : NegExponent) (T : ℝ) (hT : 1 ≤ T)
    (f g : C(ℝ, C(Torus3, ℝ))) :
    (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1), holderBesovENorm η (f t - g t)) =
      ‖windowPath η T f - windowPath η T g‖ₑ := by
  rw [window_iSup_eq T hT, windowPath, windowPath, enorm_stochasticHeatBesovPath_sub]
  rfl

private theorem potential_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (ψ : Ω → ℝ → C(Torus3, ℝ))
    (hψ : ∀ᵐ ω ∂P, ∀ t x, ψ ω t x =
      ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * ξ ω w) :
    ∃ X : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X ∧
      (ψ =ᵐ[P] fun ω t => X ω t) ∧
      ∀ t x, (fun ω => X ω t x) =ᵐ[P] stationaryField W ρ ε (t, x) := by
  obtain ⟨X, hXm, hraw⟩ :=
    regularisedNoise_massiveHeatKernel_measurable_time_paths hW ρ hρ hε ξ hξ
  refine ⟨X, hXm, ?_, ?_⟩
  · filter_upwards [hψ, hraw] with ω hω hω'
    funext t
    ext x
    exact (hω t x).trans (hω' t x).symm
  · intro t x
    filter_upwards [hraw,
      regularisedNoise_massiveHeatKernel_convolution_ae hW ρ hρ hε ξ hξ (t, x)] with ω hω hω'
    exact (hω t x).trans hω'

theorem regularisedNoise_massivePotential_window_moments
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ))
    (T : ℝ) (hT : 1 ≤ T) (p : ℕ) (hp : 1 ≤ p) :
    ∃ β C : ℝ, 0 < β ∧ 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ ξ ξ' : Ω → SpaceTime → ℝ,
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ ψ ψ' : Ω → ℝ → C(Torus3, ℝ),
      (∀ᵐ ω ∂P, ∀ t x, ψ ω t x =
        ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * ξ ω w) →
      (∀ᵐ ω ∂P, ∀ t x, ψ' ω t x =
        ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * ξ' ω w) →
      AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        holderBesovENorm η (ψ ω t)) P ∧
      AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        holderBesovENorm η (ψ ω t - ψ' ω t)) P ∧
      (∫⁻ ω, (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        holderBesovENorm η (ψ ω t)) ^ p ∂P) ≤ ENNReal.ofReal C ∧
      (∫⁻ ω, (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        holderBesovENorm η (ψ ω t - ψ' ω t)) ^ p ∂P) ≤
          ENNReal.ofReal (C * max ε ε' ^ (β * p)) := by
  obtain ⟨Cs, hCs, hsize⟩ :=
    stationaryField_version_window_size_moment_bound_uniform ρ hρ η hη T hT p
  obtain ⟨β, Cd, hβ, hCd, hdist⟩ :=
    stationaryField_version_window_cross_moment_bound_uniform ρ ρ' hρ hρ' η hη T hT p hp
  refine ⟨β, Cs + Cd, hβ, add_nonneg hCs hCd, ?_⟩
  intro Ω _ P W hW ε ε' hε hε1 hε' hε'1 ξ ξ' hξ hξ' ψ ψ' hψ hψ'
  obtain ⟨X, hXm, hXae, hX⟩ := potential_version hW ρ hρ hε ξ hξ ψ hψ
  obtain ⟨Y, hYm, hYae, hY⟩ := potential_version hW ρ' hρ' hε' ξ' hξ' ψ' hψ'
  have hAs : (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
      holderBesovENorm η (ψ ω t)) =ᵐ[P]
      (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1), holderBesovENorm η (X ω t)) := by
    filter_upwards [hXae] with ω hω
    rw [hω]
  have hAd : (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
      holderBesovENorm η (ψ ω t - ψ' ω t)) =ᵐ[P]
      (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        holderBesovENorm η (X ω t - Y ω t)) := by
    filter_upwards [hXae, hYae] with ω hω hω'
    rw [hω, hω']
  have hsm : Measurable (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
      holderBesovENorm η (X ω t)) := by
    simp_rw [window_size_eq_enorm η T hT]
    exact ((continuous_windowPath η T).measurable.comp hXm).enorm
  have hdm : Measurable (fun ω => ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
      holderBesovENorm η (X ω t - Y ω t)) := by
    simp_rw [window_dist_eq_enorm η T hT]
    exact (((continuous_windowPath η T).measurable.comp hXm).sub
      ((continuous_windowPath η T).measurable.comp hYm)).enorm
  refine ⟨hsm.aemeasurable.congr hAs.symm, hdm.aemeasurable.congr hAd.symm, ?_, ?_⟩
  · calc
      _ = ∫⁻ ω, (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
          holderBesovENorm η (X ω t)) ^ p ∂P :=
        lintegral_congr_ae (hAs.fun_comp fun a : ℝ≥0∞ => a ^ p)
      _ ≤ ENNReal.ofReal Cs := hsize hW hε hε1 X hXm hX
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hCd)
  · calc
      _ = ∫⁻ ω, (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
          holderBesovENorm η (X ω t - Y ω t)) ^ p ∂P :=
        lintegral_congr_ae (hAd.fun_comp fun a : ℝ≥0∞ => a ^ p)
      _ ≤ ENNReal.ofReal (Cd * max ε ε' ^ (β * p)) :=
        hdist hW hε hε1 hε' hε'1 X Y hXm hYm hX hY
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hCs)
        (rpow_nonneg (hε.le.trans (le_max_left _ _)) _))

end RegularityStructures.Phi43

end

