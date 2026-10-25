/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierWindowEven
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.CompletePartialOrder
public import Phi43.Stochastic.StationaryField

/-!
# Quantitative cross-mollifier convergence on [-1,T+1]

Lower the even moment after normalising by the small scale, retaining the rate. The affine
parametrisation is identified with the literal supremum over the interval `[-1,T+1]`, not a
different positive-time window. This proves the cross-mollifier moment component of the convergence
of the noise potentials (`phi43Noise_cauchy`), [Hai14, Proposition 9.5, (9.15)]. It does not assert
the growth and potential-existence components of that result.
-/

public noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace RegularityStructures.Phi43

private theorem exists_cauchy_moment_parameters
    (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ)) (p : ℝ) :
    ∃ θ : ℝ, ∃ m : ℕ, 0 < θ ∧ θ ≤ 1 ∧ 2 ≤ 2 * m ∧ 4 < (m : ℝ) * θ ∧
      3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - θ - η) ∧ p ≤ (2 * m : ℕ) := by
  let g : ℝ := -(1 / 2 : ℝ) - η
  have hg : 0 < g := sub_pos.mpr hη
  let θ := min (g / 2) (1 / 2)
  have hθ : 0 < θ := lt_min (half_pos hg) (by norm_num)
  have hθ1 : θ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hθg : θ ≤ g / 2 := min_le_left _ _
  have hgap : 0 < g - θ := by linarith only [hθg, hg]
  obtain ⟨m, hm⟩ := exists_nat_gt
    (max (max (3 / (2 * (g - θ))) (4 / θ)) (max 1 (p / 2)))
  have hm3 : 3 / (2 * (g - θ)) < (m : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hm
  have hm4 : 4 / θ < (m : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hm
  have hm1 : (1 : ℝ) < m :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hm
  have hmp : p / 2 < (m : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hm
  have hmnat : 1 < m := by exact_mod_cast hm1
  have hmθ : 4 < (m : ℝ) * θ := (div_lt_iff₀ hθ).mp hm4
  have hmgap : 3 < (m : ℝ) * (2 * (g - θ)) :=
    (div_lt_iff₀ (mul_pos (by norm_num) hgap)).mp hm3
  refine ⟨θ, m, hθ, hθ1, by omega, hmθ, ?_, ?_⟩
  · push_cast
    dsimp [g] at hmgap
    nlinarith only [hmgap]
  · push_cast
    linarith only [(div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hmp]

private theorem stationaryField_version_window_cross_rpow_moment_bound_uniform
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (η : NegExponent)
    (hη : (η : ℝ) < -(1 / 2 : ℝ)) (p : ℝ) (hp : 0 < p) (T : ℝ) (hT : 1 ≤ T) :
    ∃ β : ℝ, 0 < β ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ X Y : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X → Measurable Y →
      (∀ t y, (fun ω => X ω t y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∀ t y, (fun ω => Y ω t y) =ᵐ[P] stationaryField W ρ' ε' (t, y)) →
      (∫⁻ ω, (⨆ u : UnitInterval,
        holderBesovENorm η (X ω (((T + 2) * u - 1)) - Y ω (((T + 2) * u - 1)))) ^ p ∂P) ≤
          ENNReal.ofReal (C * (max ε ε') ^ (β * p)) := by
  obtain ⟨θ, m, hθ, hθ1, hm, hmθ, hgap, hpm⟩ := exists_cauchy_moment_parameters η hη p
  obtain ⟨C₀, hC₀, hbound⟩ := stationaryField_version_window_cross_even_moment_bound_uniform
    ρ ρ' hρ hρ' η hθ hθ1 m hm hmθ hgap T hT
  refine ⟨θ / 4, div_pos hθ (by norm_num), 1 + C₀, add_nonneg zero_le_one hC₀, ?_⟩
  intro Ω _ P W hW ε ε' hε hε1 hε' hε'1 X Y hXm hYm hX hY
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let δ := max ε ε'
  have hδ : 0 < δ := hε.trans_le (le_max_left _ _)
  let b : ℝ≥0∞ := ENNReal.ofReal (δ ^ (θ / 4))
  have hb0 : b ≠ 0 := (ENNReal.ofReal_pos.mpr (rpow_pos_of_pos hδ _)).ne'
  have hbtop : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hbp : b ^ (2 * m) = ENNReal.ofReal (δ ^ ((m : ℝ) * θ / 2)) := by
    dsimp [b]
    rw [← ENNReal.ofReal_pow (rpow_nonneg hδ.le _)]
    congr 1
    rw [← rpow_natCast, ← rpow_mul hδ.le]
    congr 1
    push_cast
    ring
  have hN : (∫⁻ ω, (⨆ u : UnitInterval,
      holderBesovENorm η (X ω (((T + 2) * u - 1)) - Y ω (((T + 2) * u - 1)))) ^ (2 * m) ∂P) ≤
        ENNReal.ofReal C₀ * b ^ (2 * m) := by
    rw [hbp, ← ENNReal.ofReal_mul hC₀]
    exact hbound hW hε hε1 hε' hε'1 X Y hXm hYm hX hY
  have hlower := lintegral_rpow_le_of_scaled_natMoment hp.le hpm hb0 hbtop hN
  have hbp' : b ^ p = ENNReal.ofReal (δ ^ ((θ / 4) * p)) := by
    dsimp [b]
    rw [ENNReal.ofReal_rpow_of_nonneg (rpow_nonneg hδ.le _) hp.le, ← rpow_mul hδ.le]
  apply hlower.trans_eq
  rw [hbp', ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hC₀,
    ← ENNReal.ofReal_mul (add_nonneg zero_le_one hC₀)]

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

theorem stationaryField_version_window_cross_moment_bound_uniform
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ))
    (T : ℝ) (hT : 1 ≤ T) (p : ℕ) (hp : 1 ≤ p) :
    ∃ β C : ℝ, 0 < β ∧ 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ X Y : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X → Measurable Y →
      (∀ t y, (fun ω => X ω t y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∀ t y, (fun ω => Y ω t y) =ᵐ[P] stationaryField W ρ' ε' (t, y)) →
      (∫⁻ ω, (⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        holderBesovENorm η (X ω t - Y ω t)) ^ p ∂P) ≤
          ENNReal.ofReal (C * max ε ε' ^ (β * p)) := by
  obtain ⟨β, hβ, C, hC, hb⟩ := stationaryField_version_window_cross_rpow_moment_bound_uniform
    ρ ρ' hρ hρ' η hη p (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)) T hT
  refine ⟨β, C, hβ, hC, ?_⟩
  intro Ω _ P W hW ε ε' hε hε1 hε' hε'1 X Y hXm hYm hX hY
  have h := hb hW hε hε1 hε' hε'1 X Y hXm hYm hX hY
  simp_rw [window_iSup_eq T hT]
  simpa only [ENNReal.rpow_natCast] using h

end RegularityStructures.Phi43

end

