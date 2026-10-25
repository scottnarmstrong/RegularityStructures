/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.CompletePartialOrder
public import Phi43.Stochastic.StationaryField
public import Phi43.Stochastic.StochasticHeatConvergenceBesovIncrements
public import Phi43.Stochastic.StochasticHeatConvergencePathSup
public import RegularityStructures.Probability.KolmogorovChentsovHolderBesov

/-!
# Uniform potential-size moments on the time window `[-1,T+1]`

The time-increment estimates are uniform at every real time. Applying the compact
maximal criterion to `(T+2)u-1` gives the size bound on `[-1,T+1]`.
This is the size component of the convergence of the noise potentials (`phi43Noise_cauchy`),
[Hai14, Proposition 9.5, (9.15)].
-/

public noncomputable section

open MeasureTheory Real
open scoped ENNReal NNReal Topology

namespace RegularityStructures.Phi43

private theorem window_even_moment_bound
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) (η : NegExponent)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (m : ℕ) (hm : 2 ≤ 2 * m)
    (hmθ : 2 < (m : ℝ) * θ)
    (hgap : 3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - θ - η))
    (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ X : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X →
      (∀ t : ℝ, ∀ y : Torus3, (fun ω => X ω t y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∫⁻ ω, (⨆ u : UnitInterval, holderBesovENorm η (X ω (((T + 2) * u - 1)))) ^ (2 * m) ∂P) ≤
        ENNReal.ofReal C := by
  have hlen : 0 < T + 2 := by linarith only [hT]
  have hsizegap : 3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - η) := by
    have hprod : 0 ≤ (2 * m : ℕ) * θ := mul_nonneg (Nat.cast_nonneg _) hθ.le
    nlinarith only [hgap, hprod]
  obtain ⟨B, hB, hsize⟩ :=
    stationaryField_version_holderBesov_even_moment_bound_uniform ρ hρ η m hm hsizegap
  obtain ⟨M, hM, htime⟩ :=
    stationaryField_version_holderBesov_time_even_moment_bound_uniform ρ hρ η hθ.le hθ1 m hm hgap
  let q := (m : ℝ) * θ
  let r : ℝ≥0 := ⟨θ / 4, (div_pos hθ (by norm_num)).le⟩
  have hr : 0 < r := by change 0 < θ / 4; exact div_pos hθ (by norm_num)
  have hq : 0 ≤ q := (show 0 < (m : ℝ) * θ by linarith only [hmθ]).le
  have hpr : (2 * m : ℕ) * (r : ℝ) < q - 1 := by
    change (2 * m : ℕ) * (θ / 4) < (m : ℝ) * θ - 1
    push_cast
    linarith only [hmθ]
  obtain ⟨D, hD, hmax⟩ := continuous_process_sup_norm_moment_bound
    (p := 2 * m) (q := q) (r := r)
    (M := ENNReal.ofReal (M * (T + 2) ^ q)) (B := ENNReal.ofReal B)
    (by omega) hq hr hpr ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨D.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ω _ P W hW ε hε hε1 X hXm hX
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let F : UnitInterval → Ω → C(Torus3, ℝ) := fun u ω => X ω (((T + 2) * u - 1))
  let Z : UnitInterval → Ω → HolderBesov η := fun u ω => toHolderBesov η (F u ω)
  have hFm (u : UnitInterval) : Measurable (F u) :=
    (ContinuousMap.measurable_eval (((T + 2) * u - 1))).comp hXm
  have hdiffm (u v : UnitInterval) : Measurable (fun ω => F u ω - F v ω) :=
    ContinuousMap.measurable_iff_eval.mpr fun x =>
      ((ContinuousMap.measurable_eval x).comp (hFm u)).sub
        ((ContinuousMap.measurable_eval x).comp (hFm v))
  have hedist (u v : UnitInterval) (ω : Ω) :
      edist (Z u ω) (Z v ω) = holderBesovENorm η (F u ω - F v ω) := by
    rw [edist_eq_enorm_sub, ← toHolderBesov_sub, enorm_toHolderBesov]
  have hZcont (ω : Ω) : Continuous (Z · ω) := by
    exact (toHolderBesov_lipschitzWith η).continuous.comp
      ((X ω).continuous.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const))
  have hZmeas (u v : UnitInterval) : AEMeasurable (fun ω => edist (Z u ω) (Z v ω)) P := by
    simp_rw [hedist]
    exact ((continuous_holderBesovENorm_negative η).measurable.comp (hdiffm u v)).aemeasurable
  have hpair (u v : UnitInterval) :
      (∫⁻ ω, edist (Z u ω) (Z v ω) ^ (2 * m) ∂P) ≤
        ENNReal.ofReal (M * (T + 2) ^ q) * edist u v ^ q := by
    simp_rw [hedist]
    have hb := htime hW hε hε1 (((T + 2) * u - 1)) (((T + 2) * v - 1)) (F u) (F v) (hFm u) (hFm v)
      (hX (((T + 2) * u - 1))) (hX (((T + 2) * v - 1)))
    apply hb.trans_eq
    have he : |((T + 2) * (u : ℝ) - 1) - ((T + 2) * (v : ℝ) - 1)| =
        (T + 2) * |(u : ℝ) - v| := by
      have ha : ((T + 2) * (u : ℝ) - 1) - ((T + 2) * (v : ℝ) - 1) =
          (T + 2) * ((u : ℝ) - v) := by ring
      rw [ha, abs_mul, abs_of_pos hlen]
    rw [he, mul_rpow hlen.le (abs_nonneg _), ← mul_assoc,
      ENNReal.ofReal_mul (mul_nonneg hM (rpow_nonneg hlen.le _))]
    change ENNReal.ofReal (M * (T + 2) ^ q) * ENNReal.ofReal (|(u : ℝ) - v| ^ q) = _
    rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq]
    congr 1
    rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
  have h0meas : AEMeasurable (fun ω => ‖Z 0 ω‖ₑ) P := by
    simp only [Z, enorm_toHolderBesov]
    exact ((continuous_holderBesovENorm_negative η).measurable.comp (hFm 0)).aemeasurable
  have hinit : (∫⁻ ω, ‖Z 0 ω‖ₑ ^ (2 * m) ∂P) ≤ ENNReal.ofReal B := by
    simp only [Z, enorm_toHolderBesov]
    exact hsize hW hε hε1 (((T + 2) * (0 : UnitInterval) - 1)) (F 0) (hFm 0) (hX _)
  have hs := hmax Z hZcont hZmeas hpair h0meas hinit
  rw [ENNReal.ofReal_toReal hD]
  simpa only [Z, F, enorm_toHolderBesov] using hs

private theorem exists_path_moment_parameters
    (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ)) (p : ℝ) :
    ∃ θ : ℝ, ∃ m : ℕ, 0 < θ ∧ θ ≤ 1 ∧ 2 ≤ 2 * m ∧ 2 < (m : ℝ) * θ ∧
      3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - θ - η) ∧ p ≤ (2 * m : ℕ) := by
  let g : ℝ := -(1 / 2 : ℝ) - η
  have hg : 0 < g := sub_pos.mpr hη
  let θ := min (g / 2) (1 / 2)
  have hθ : 0 < θ := lt_min (half_pos hg) (by norm_num)
  have hθ1 : θ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hθg : θ ≤ g / 2 := min_le_left _ _
  have hgap : 0 < g - θ := by linarith only [hθg, hg]
  obtain ⟨m, hm⟩ := exists_nat_gt
    (max (max (3 / (2 * (g - θ))) (2 / θ)) (max 1 (p / 2)))
  have hm3 : 3 / (2 * (g - θ)) < (m : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hm
  have hm2 : 2 / θ < (m : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hm
  have hm1 : (1 : ℝ) < m :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hm
  have hmp : p / 2 < (m : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hm
  have hmnat : 1 < m := by exact_mod_cast hm1
  have hmθ : 2 < (m : ℝ) * θ := (div_lt_iff₀ hθ).mp hm2
  have hmgap : 3 < (m : ℝ) * (2 * (g - θ)) :=
    (div_lt_iff₀ (mul_pos (by norm_num) hgap)).mp hm3
  refine ⟨θ, m, hθ, hθ1, by omega, hmθ, ?_, ?_⟩
  · push_cast
    dsimp [g] at hmgap
    nlinarith only [hmgap]
  · push_cast
    linarith only [(div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hmp]

private theorem window_rpow_moment_bound
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) (η : NegExponent)
    (hη : (η : ℝ) < -(1 / 2 : ℝ)) (p : ℝ) (hp : 0 ≤ p) (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ X : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X →
      (∀ t : ℝ, ∀ y : Torus3, (fun ω => X ω t y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∫⁻ ω, (⨆ u : UnitInterval, holderBesovENorm η (X ω (((T + 2) * u - 1)))) ^ p ∂P) ≤
        ENNReal.ofReal C := by
  obtain ⟨θ, m, hθ, hθ1, hm, hmθ, hgap, hpm⟩ := exists_path_moment_parameters η hη p
  obtain ⟨C₀, hC₀, hbound⟩ := window_even_moment_bound
    ρ hρ η hθ hθ1 m hm hmθ hgap T hT
  refine ⟨1 + C₀, add_nonneg zero_le_one hC₀, ?_⟩
  intro Ω _ P W hW ε hε hε1 X hXm hX
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hpoint (a : ℝ≥0∞) : a ^ p ≤ 1 + a ^ (2 * m) := by
    by_cases ha : a ≤ 1
    · exact (ENNReal.rpow_le_one ha hp).trans (le_add_of_nonneg_right zero_le)
    · have hpow := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge ha) hpm
      rw [ENNReal.rpow_natCast] at hpow
      exact hpow.trans (le_add_of_nonneg_left zero_le)
  calc
    _ ≤ ∫⁻ ω, 1 + (⨆ u : UnitInterval, holderBesovENorm η (X ω (((T + 2) * u - 1)))) ^ (2 * m) ∂P :=
      lintegral_mono fun ω => hpoint _
    _ = 1 + ∫⁻ ω, (⨆ u : UnitInterval, holderBesovENorm η (X ω (((T + 2) * u - 1)))) ^ (2 * m) ∂P := by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal C₀ := add_le_add_right (hbound hW hε hε1 X hXm hX) _
    _ = ENNReal.ofReal (1 + C₀) := by rw [ENNReal.ofReal_add zero_le_one hC₀, ENNReal.ofReal_one]

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

theorem stationaryField_version_window_size_moment_bound_uniform
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (η : NegExponent)
    (hη : (η : ℝ) < -(1 / 2 : ℝ)) (T : ℝ) (hT : 1 ≤ T) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∀ X : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X →
      (∀ t y, (fun ω => X ω t y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∫⁻ ω, (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        holderBesovENorm η (X ω t)) ^ p ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := window_rpow_moment_bound ρ hρ η hη p (Nat.cast_nonneg _) T hT
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W hW ε hε hε1 X hXm hX
  simp_rw [window_iSup_eq T hT]
  simpa only [ENNReal.rpow_natCast] using hb hW hε hε1 X hXm hX

end RegularityStructures.Phi43

end

