/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierBounds
public import Phi43.Stochastic.StochasticHeatConvergenceBesovIncrements
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Cross-mollifier moments in the pinned heat--Besov norm

Gaussian heat-probe bounds pass to arbitrary measurable continuous modifications, then to the norm
(2.3) of the statement by the spatial Kolmogorov criterion. This is the spatial moment input to the
convergence of the noise potentials (`phi43Noise_cauchy`) [Hai14, Proposition 9.5, (9.14)--(9.15)];
neither a covariance bound nor a version identification is assumed.
-/

public noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem stationaryField_version_heat_cross_even_moment_bound_uniform
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → ∀ t : ℝ,
      ∀ X Y : Ω → C(Torus3, ℝ), Measurable X → Measurable Y →
      (∀ y, (fun ω => X ω y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∀ y, (fun ω => Y ω y) =ᵐ[P] stationaryField W ρ' ε' (t, y)) →
      ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ x : Torus3,
      (∫ ω, |heatSemigroup s (X ω - Y ω) x| ^ (2 * m) ∂P) ≤
        C * (max ε ε') ^ ((m : ℝ) * θ) * s ^ (-((m : ℝ) / 2 + (m : ℝ) * θ)) := by
  obtain ⟨C, hC, hbound⟩ := stochasticHeatField_cross_difference_even_moment_bound_uniform ρ ρ' hρ hρ' hθ hθ1 m
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W hW ε ε' hε hε1 hε' hε'1 t X Y hXm hYm hX hY s hs hs1 x
  calc
    _ = ∫ ω, |stochasticHeatField W ρ ε s (t, x) ω -
        stochasticHeatField W ρ' ε' s (t, x) ω| ^ (2 * m) ∂P := by
      apply integral_congr_ae
      filter_upwards [heatSemigroup_stationaryField_version_ae hW ρ hρ hε hXm hX hs x,
        heatSemigroup_stationaryField_version_ae hW ρ' hρ' hε' hYm hY hs x] with ω hω hω'
      rw [sub_eq_add_neg, heatSemigroup_add hs, heatSemigroup_neg, hω, hω']
      rfl
    _ ≤ _ := hbound hW hε hε1 hε' hε'1 hs hs1 (t, x)

private theorem besov_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {ε ε' t t' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    {X Y : Ω → C(Torus3, ℝ)} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : ∀ y, (fun ω => X ω y) =ᵐ[P] stationaryField W ρ ε (t, y))
    (hY : ∀ y, (fun ω => Y ω y) =ᵐ[P] stationaryField W ρ' ε' (t', y))
    (η : NegExponent) {θ δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (m : ℕ) (hm : 2 ≤ 2 * m)
    (hgap : 3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - θ - η))
    (hbound : ∀ {r : ℝ}, 0 < r → r ≤ 1 → ∀ x : Torus3,
      (∫ ω, |heatSemigroup r (X ω - Y ω) x| ^ (2 * m) ∂P) ≤
        C * δ ^ ((m : ℝ) * θ) * r ^ (-((m : ℝ) / 2 + (m : ℝ) * θ))) :
    (∫⁻ ω, holderBesovENorm η (X ω - Y ω) ^ (2 * m) ∂P) ≤
      ENNReal.ofReal (kolmogorovHolderBesovConstant (2 * m) (-(1 / 2 : ℝ) - θ) η *
        (C + 1) ^ (2 * m) * δ ^ ((m : ℝ) * θ)) := by
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let A := C + 1
  let B := A * δ ^ (θ / 2)
  have hA : 0 ≤ A := add_nonneg hC zero_le_one
  have hAone : 1 ≤ A := by dsimp [A]; linarith only [hC]
  have hCA : C ≤ A ^ (2 * m) :=
    (show C ≤ A from le_add_of_nonneg_right zero_le_one).trans (le_self_pow₀ hAone (by omega))
  have hB : 0 ≤ B := mul_nonneg hA (rpow_nonneg hδ _)
  have hBp : B ^ (2 * m) = A ^ (2 * m) * δ ^ ((m : ℝ) * θ) := by
    dsimp [B]
    rw [mul_pow]
    congr 1
    rw [← rpow_natCast, ← rpow_mul hδ]
    congr 1
    push_cast
    ring
  have hFm : Measurable (fun ω => X ω - Y ω) :=
    ContinuousMap.measurable_iff_eval.mpr fun x =>
      ((ContinuousMap.measurable_eval x).comp hXm).sub ((ContinuousMap.measurable_eval x).comp hYm)
  have hout : (∫⁻ ω, holderBesovENorm η (X ω - Y ω) ^ (2 * m) ∂P) ≤
      ENNReal.ofReal (kolmogorovHolderBesovConstant (2 * m) (-(1 / 2 : ℝ) - θ) η *
        B ^ (2 * m)) := by
    apply holderBesovENorm_natMoment_le_of_pointwise η.2.le hm hgap hB
    · exact ((continuous_holderBesovENorm_negative η).measurable.comp hFm).aemeasurable
    · intro n
      exact ((continuous_dyadicHolderBesovTerm η n).measurable.comp hFm).aemeasurable
    · intro r hr _
      exact (((continuous_heatSemigroup_apply hr).measurable.comp
        (hFm.prodMap measurable_id)).enorm.pow_const (2 * m)).aemeasurable
    · intro r hr hr1 x
      have hk : MemLp (stochasticHeatKernel ρ ε r (t, x)) 2 :=
        memLp_stochasticHeatKernel_of_integrable_square ρ hρ hε hr (t, x)
          (integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts ρ hρ hε hr (t, x))
      have hk' : MemLp (stochasticHeatKernel ρ' ε' r (t', x)) 2 :=
        memLp_stochasticHeatKernel_of_integrable_square ρ' hρ' hε' hr (t', x)
          (integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts ρ' hρ' hε' hr (t', x))
      let k := stochasticHeatKernel ρ ε r (t, x) - stochasticHeatKernel ρ' ε' r (t', x)
      have hkl : MemLp k 2 := hk.sub hk'
      have heq : (fun ω => heatSemigroup r (X ω - Y ω) x) =ᵐ[P] W k := by
        filter_upwards [heatSemigroup_stationaryField_version_ae hW ρ hρ hε hXm hX hr x,
          heatSemigroup_stationaryField_version_ae hW ρ' hρ' hε' hYm hY hr x,
          whiteNoise_pairing_sub_ae hW hk hk'] with ω hω hω' hsub
        rw [sub_eq_add_neg, heatSemigroup_add hr, heatSemigroup_neg, hω, hω']
        exact hsub
      have hi0 : Integrable (fun ω => |W k ω| ^ (2 * m)) P := by
        simpa only [Real.norm_eq_abs, abs_pow] using
          ((whiteNoise_pairing_hasGaussianLaw hW hkl).integrable_pow (2 * m)).norm
      have hi : Integrable (fun ω => |heatSemigroup r (X ω - Y ω) x| ^ (2 * m)) P :=
        hi0.congr (heq.symm.fun_comp (fun a : ℝ => |a| ^ (2 * m)))
      have hen (ω : Ω) : ‖heatSemigroup r (X ω - Y ω) x‖ₑ ^ (2 * m) =
          ENNReal.ofReal (|heatSemigroup r (X ω - Y ω) x| ^ (2 * m)) := by
        rw [ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]
      simp_rw [hen]
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) _)]
      apply ENNReal.ofReal_le_ofReal
      have hexp : (-(1 / 2 : ℝ) - θ) * (2 * m : ℕ) / 2 =
          -((m : ℝ) / 2 + (m : ℝ) * θ) := by push_cast; ring
      rw [hexp, hBp]
      exact (hbound hr hr1 x).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCA (rpow_nonneg hδ _)) (rpow_nonneg hr.le _))
  simpa only [hBp, mul_assoc] using hout

theorem stationaryField_version_holderBesov_cross_even_moment_bound_uniform
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (η : NegExponent)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℕ) (hm : 2 ≤ 2 * m)
    (hgap : 3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - θ - η)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → ∀ t : ℝ,
      ∀ X Y : Ω → C(Torus3, ℝ), Measurable X → Measurable Y →
      (∀ y, (fun ω => X ω y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∀ y, (fun ω => Y ω y) =ᵐ[P] stationaryField W ρ' ε' (t, y)) →
      (∫⁻ ω, holderBesovENorm η (X ω - Y ω) ^ (2 * m) ∂P) ≤
        ENNReal.ofReal (C * (max ε ε') ^ ((m : ℝ) * θ)) := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    stationaryField_version_heat_cross_even_moment_bound_uniform ρ ρ' hρ hρ' hθ hθ1 m
  refine ⟨kolmogorovHolderBesovConstant (2 * m) (-(1 / 2 : ℝ) - θ) η * (C₀ + 1) ^ (2 * m),
    mul_nonneg (kolmogorovHolderBesovConstant_nonneg hgap) (pow_nonneg (by linarith only [hC₀]) _), ?_⟩
  intro Ω _ P W hW ε ε' hε hε1 hε' hε'1 t X Y hXm hYm hX hY
  exact besov_pair_bound hW ρ ρ' hρ hρ' hε hε' hXm hYm hX hY η (hε.le.trans (le_max_left _ _))
    hC₀ m hm hgap (fun hr hr1 x => hbound hW hε hε1 hε' hε'1 t X Y hXm hYm hX hY hr hr1 x)

end RegularityStructures.Phi43

end

