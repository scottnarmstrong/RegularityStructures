/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceVersionMoments
public import Phi43.Stochastic.StochasticHeatConvergenceBesovMeasurability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Uniform fixed-time Besov moments of stationary continuous versions

The uniform heat moment bound and the spatial Kolmogorov criterion yield fixed-time
negative Besov moments whenever the even moment order times the regularity gap exceeds three.
All constants are uniform in the regularisation scale and in the measurable continuous version.
The norm is the norm (2.3) of the statement.
-/

public noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem stationaryField_version_holderBesov_even_moment_bound_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) (η : NegExponent)
    (m : ℕ) (hm : 2 ≤ 2 * m) (hgap : 3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - η)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ t : ℝ, ∀ X : Ω → C(Torus3, ℝ), Measurable X →
      (∀ y, (fun ω => X ω y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∫⁻ ω, holderBesovENorm η (X ω) ^ (2 * m) ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀, hbound⟩ := stationaryField_version_heat_even_moment_bound_uniform ρ hρ m
  let A := C₀ + 1
  have hA : 0 ≤ A := add_nonneg hC₀ zero_le_one
  have hAone : 1 ≤ A := by dsimp [A]; linarith only [hC₀]
  have hCA : C₀ ≤ A ^ (2 * m) :=
    (show C₀ ≤ A from le_add_of_nonneg_right zero_le_one).trans
      (le_self_pow₀ hAone (by omega))
  refine ⟨kolmogorovHolderBesovConstant (2 * m) (-(1 / 2 : ℝ)) η * A ^ (2 * m),
    mul_nonneg (kolmogorovHolderBesovConstant_nonneg hgap) (pow_nonneg hA _), ?_⟩
  intro Ω _ P W hW ε hε hε1 t X hXm hX
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  apply holderBesovENorm_natMoment_le_of_pointwise η.2.le hm hgap hA
  · exact ((continuous_holderBesovENorm_negative η).measurable.comp hXm).aemeasurable
  · intro n
    exact ((continuous_dyadicHolderBesovTerm η n).measurable.comp hXm).aemeasurable
  · intro r hr _
    exact (((continuous_heatSemigroup_apply hr).measurable.comp
      (hXm.prodMap measurable_id)).enorm.pow_const (2 * m)).aemeasurable
  · intro r hr hr1 y
    have hK : MemLp (stochasticHeatKernel ρ ε r (t, y)) 2 :=
      memLp_stochasticHeatKernel_of_integrable_square ρ hρ hε hr (t, y)
        (integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts ρ hρ hε hr (t, y))
    have hgauss := whiteNoise_pairing_hasGaussianLaw hW hK
    have hpow : Integrable (fun ω => |stochasticHeatField W ρ ε r (t, y) ω| ^ (2 * m)) P := by
      simpa only [stochasticHeatField, Real.norm_eq_abs, abs_pow] using (hgauss.integrable_pow (2 * m)).norm
    have hpair := heatSemigroup_stationaryField_version_ae hW ρ hρ hε hXm hX hr y
    have hi : Integrable (fun ω => |heatSemigroup r (X ω) y| ^ (2 * m)) P :=
      hpow.congr (hpair.symm.fun_comp (fun a : ℝ => |a| ^ (2 * m)))
    have hen (ω : Ω) : ‖heatSemigroup r (X ω) y‖ₑ ^ (2 * m) =
        ENNReal.ofReal (|heatSemigroup r (X ω) y| ^ (2 * m)) := by
      rw [ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]
    simp_rw [hen]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) _)]
    apply ENNReal.ofReal_le_ofReal
    have hexp : (-(1 / 2 : ℝ)) * (2 * m : ℕ) / 2 = -((m : ℝ) / 2) := by
      push_cast
      ring
    rw [hexp]
    exact (hbound hW hε hε1 t X hXm hX hr hr1 y).trans
      (mul_le_mul_of_nonneg_right hCA (rpow_nonneg hr.le _))

end RegularityStructures.Phi43

end
