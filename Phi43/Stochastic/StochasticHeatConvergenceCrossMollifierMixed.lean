/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierBesov
public import Phi43.Stochastic.StochasticHeatConvergenceCauchyTools
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Phi43.Stochastic.StationaryField
public import RegularityStructures.Probability.KolmogorovChentsovHolderBesov

/-!
# Mixed time and cross-mollifier increments

The two profiles have separate uniform time moduli and a common small cross-scale modulus.
Geometric-mean interpolation retains both gains, as needed for the compact time supremum in the
convergence of the noise potentials (`phi43Noise_cauchy`) [Hai14, Proposition 9.5, (9.15)].
-/

public noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace RegularityStructures.Phi43

private theorem measurable_spatial_sub
    {Ω : Type*} [MeasurableSpace Ω] {U V : Ω → C(Torus3, ℝ)}
    (hU : Measurable U) (hV : Measurable V) : Measurable (fun ω => U ω - V ω) :=
  ContinuousMap.measurable_iff_eval.mpr fun x =>
    ((ContinuousMap.measurable_eval x).comp hU).sub ((ContinuousMap.measurable_eval x).comp hV)

private theorem besov_sub_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U V : Ω → C(Torus3, ℝ)}
    (hU : Measurable U) (hV : Measurable V) (η : NegExponent) (p : ℕ) :
    (∫⁻ ω, holderBesovENorm η (U ω - V ω) ^ p ∂P) ≤ (2 : ℝ≥0∞) ^ p *
      ((∫⁻ ω, holderBesovENorm η (U ω) ^ p ∂P) + ∫⁻ ω, holderBesovENorm η (V ω) ^ p ∂P) := by
  have hUm : AEMeasurable (fun ω => ‖toHolderBesov η (U ω)‖ₑ) P := by
    simpa only [enorm_toHolderBesov, Function.comp_def] using
      ((continuous_holderBesovENorm_negative η).measurable.comp hU).aemeasurable
  have hVm : AEMeasurable (fun ω => ‖toHolderBesov η (V ω)‖ₑ) P := by
    simpa only [enorm_toHolderBesov, Function.comp_def] using
      ((continuous_holderBesovENorm_negative η).measurable.comp hV).aemeasurable
  simpa only [← toHolderBesov_sub, enorm_toHolderBesov] using
    lintegral_enorm_sub_natPow_le hUm hVm p

theorem stationaryField_version_holderBesov_cross_mixed_even_moment_bound_uniform
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (η : NegExponent)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℕ) (hm : 2 ≤ 2 * m)
    (hgap : 3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - θ - η)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ X Y : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X → Measurable Y →
      (∀ t y, (fun ω => X ω t y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∀ t y, (fun ω => Y ω t y) =ᵐ[P] stationaryField W ρ' ε' (t, y)) →
      ∀ t t' : ℝ,
      (∫⁻ ω, holderBesovENorm η ((X ω t - Y ω t) - (X ω t' - Y ω t')) ^ (2 * m) ∂P) ≤
        ENNReal.ofReal (C * (max ε ε') ^ ((m : ℝ) * θ / 2) * |t - t'| ^ ((m : ℝ) * θ / 2)) := by
  obtain ⟨Ct, hCt, htime⟩ :=
    stationaryField_version_holderBesov_time_even_moment_bound_uniform ρ hρ η hθ hθ1 m hm hgap
  obtain ⟨Ct', hCt', htime'⟩ :=
    stationaryField_version_holderBesov_time_even_moment_bound_uniform ρ' hρ' η hθ hθ1 m hm hgap
  obtain ⟨Cs, hCs, hscale⟩ :=
    stationaryField_version_holderBesov_cross_even_moment_bound_uniform ρ ρ' hρ hρ' η hθ hθ1 m hm hgap
  let M := max (max Ct Ct') Cs
  have hM : 0 ≤ M := hCt.trans ((le_max_left _ _).trans (le_max_left _ _))
  let K : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (2 * m) * (ENNReal.ofReal M + ENNReal.ofReal M)
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (by simp) (by simp)
  refine ⟨K.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ω _ P W hW ε ε' hε hε1 hε' hε'1 X Y hXm hYm hX hY t t'
  let q := (m : ℝ) * θ
  let δ := max ε ε'
  have hδ : 0 ≤ δ := hε.le.trans (le_max_left _ _)
  have hXm' (u : ℝ) : Measurable (fun ω => X ω u) := (ContinuousMap.measurable_eval u).comp hXm
  have hYm' (u : ℝ) : Measurable (fun ω => Y ω u) := (ContinuousMap.measurable_eval u).comp hYm
  let A : ℝ≥0∞ := ∫⁻ ω,
    holderBesovENorm η ((X ω t - Y ω t) - (X ω t' - Y ω t')) ^ (2 * m) ∂P
  have hs (u : ℝ) : (∫⁻ ω, holderBesovENorm η (X ω u - Y ω u) ^ (2 * m) ∂P) ≤
      ENNReal.ofReal (M * δ ^ q) :=
    (hscale hW hε hε1 hε' hε'1 u (fun ω => X ω u) (fun ω => Y ω u)
      (hXm' u) (hYm' u) (hX u) (hY u)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) (rpow_nonneg hδ _)))
  have hscaleA : A ≤ K * ENNReal.ofReal (δ ^ q) := by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ (2 * m) *
          ((∫⁻ ω, holderBesovENorm η (X ω t - Y ω t) ^ (2 * m) ∂P) +
            ∫⁻ ω, holderBesovENorm η (X ω t' - Y ω t') ^ (2 * m) ∂P) :=
        besov_sub_moment_le (measurable_spatial_sub (hXm' t) (hYm' t))
          (measurable_spatial_sub (hXm' t') (hYm' t')) η _
      _ ≤ (2 : ℝ≥0∞) ^ (2 * m) * (ENNReal.ofReal (M * δ ^ q) + ENNReal.ofReal (M * δ ^ q)) :=
        mul_le_mul_right (add_le_add (hs t) (hs t')) _
      _ = K * ENNReal.ofReal (δ ^ q) := by rw [ENNReal.ofReal_mul hM]; dsimp [K]; ring
  have htX : (∫⁻ ω, holderBesovENorm η (X ω t - X ω t') ^ (2 * m) ∂P) ≤
      ENNReal.ofReal (M * |t - t'| ^ q) :=
    (htime hW hε hε1 t t' (fun ω => X ω t) (fun ω => X ω t')
      (hXm' t) (hXm' t') (hX t) (hX t')).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (rpow_nonneg (abs_nonneg _) _)))
  have htY : (∫⁻ ω, holderBesovENorm η (Y ω t - Y ω t') ^ (2 * m) ∂P) ≤
      ENNReal.ofReal (M * |t - t'| ^ q) :=
    (htime' hW hε' hε'1 t t' (fun ω => Y ω t) (fun ω => Y ω t')
      (hYm' t) (hYm' t') (hY t) (hY t')).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (rpow_nonneg (abs_nonneg _) _)))
  have htimeA : A ≤ K * ENNReal.ofReal (|t - t'| ^ q) := by
    calc
      _ = ∫⁻ ω, holderBesovENorm η ((X ω t - X ω t') - (Y ω t - Y ω t')) ^ (2 * m) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        congr 2
        abel
      _ ≤ (2 : ℝ≥0∞) ^ (2 * m) *
          ((∫⁻ ω, holderBesovENorm η (X ω t - X ω t') ^ (2 * m) ∂P) +
            ∫⁻ ω, holderBesovENorm η (Y ω t - Y ω t') ^ (2 * m) ∂P) :=
        besov_sub_moment_le (measurable_spatial_sub (hXm' t) (hXm' t'))
          (measurable_spatial_sub (hYm' t) (hYm' t')) η _
      _ ≤ (2 : ℝ≥0∞) ^ (2 * m) *
          (ENNReal.ofReal (M * |t - t'| ^ q) + ENNReal.ofReal (M * |t - t'| ^ q)) :=
        mul_le_mul_right (add_le_add htX htY) _
      _ = K * ENNReal.ofReal (|t - t'| ^ q) := by rw [ENNReal.ofReal_mul hM]; dsimp [K]; ring
  have hroot (a : ℝ) (ha : 0 ≤ a) :
      (ENNReal.ofReal (a ^ q)) ^ (1 / 2 : ℝ) = ENNReal.ofReal (a ^ (q / 2)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (rpow_nonneg ha _) (by norm_num), ← rpow_mul ha]
    congr 2
    ring
  have hmix := ennreal_le_geometric_mean_of_two_bounds hscaleA htimeA
  rw [hroot δ hδ, hroot |t - t'| (abs_nonneg _)] at hmix
  apply hmix.trans_eq
  conv_lhs => rw [← ENNReal.ofReal_toReal hK]
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (rpow_nonneg hδ _))]

end RegularityStructures.Phi43

end

