/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierMixed
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.CompletePartialOrder
public import Phi43.Stochastic.StationaryField
public import RegularityStructures.Probability.KolmogorovChentsovHolderBesov

/-!
# Cross-mollifier path moments on the time window `[-1,T+1]`

Parametrise the interval `[-1,T+1]` by `(T+2)u-1`, for `u ∈ [0,1]`.
The scale-preserving maximal criterion yields even moments retaining a positive
power of the larger mollifier scale. This is the high-moment step for
the convergence of the noise potentials (`phi43Noise_cauchy`), [Hai14, Proposition 9.5, (9.15)].
-/

public noncomputable section

open MeasureTheory Real
open scoped ENNReal NNReal Topology

namespace RegularityStructures.Phi43

private theorem measurable_spatial_sub
    {Ω : Type*} [MeasurableSpace Ω] {U V : Ω → C(Torus3, ℝ)}
    (hU : Measurable U) (hV : Measurable V) : Measurable (fun ω => U ω - V ω) :=
  ContinuousMap.measurable_iff_eval.mpr fun x =>
    ((ContinuousMap.measurable_eval x).comp hU).sub ((ContinuousMap.measurable_eval x).comp hV)

theorem stationaryField_version_window_cross_even_moment_bound_uniform
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (η : NegExponent)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (m : ℕ) (hm : 2 ≤ 2 * m)
    (hmθ : 4 < (m : ℝ) * θ)
    (hgap : 3 < (2 * m : ℕ) * (-(1 / 2 : ℝ) - θ - η))
    (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ X Y : Ω → C(ℝ, C(Torus3, ℝ)), Measurable X → Measurable Y →
      (∀ t y, (fun ω => X ω t y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∀ t y, (fun ω => Y ω t y) =ᵐ[P] stationaryField W ρ' ε' (t, y)) →
      (∫⁻ ω, (⨆ u : UnitInterval,
        holderBesovENorm η (X ω (((T + 2) * u - 1)) - Y ω (((T + 2) * u - 1)))) ^ (2 * m) ∂P) ≤
          ENNReal.ofReal (C * (max ε ε') ^ ((m : ℝ) * θ / 2)) := by
  have hlen : 0 < T + 2 := by linarith only [hT]
  obtain ⟨B, hB, hscale⟩ :=
    stationaryField_version_holderBesov_cross_even_moment_bound_uniform ρ ρ' hρ hρ' η hθ.le hθ1 m hm hgap
  obtain ⟨M, hM, hmix⟩ :=
    stationaryField_version_holderBesov_cross_mixed_even_moment_bound_uniform ρ ρ' hρ hρ' η hθ.le hθ1 m hm hgap
  let q := (m : ℝ) * θ / 2
  let r : ℝ≥0 := ⟨θ / 8, (div_pos hθ (by norm_num)).le⟩
  have hr : 0 < r := by change 0 < θ / 8; exact div_pos hθ (by norm_num)
  have hq : 0 ≤ q := by dsimp [q]; linarith only [hmθ]
  have hpr : (2 * m : ℕ) * (r : ℝ) < q - 1 := by
    change (2 * m : ℕ) * (θ / 8) < (m : ℝ) * θ / 2 - 1
    push_cast
    linarith only [hmθ]
  obtain ⟨K, hK, hmax⟩ := continuous_process_sup_norm_moment_bound_scaled
    (p := 2 * m) (q := q) (r := r) (by omega) hq hr hpr
  let L := K * (ENNReal.ofReal B + ENNReal.ofReal (M * (T + 2) ^ q))
  have hL : L ≠ ∞ := ENNReal.mul_ne_top hK (by simp)
  refine ⟨L.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ω _ P W hW ε ε' hε hε1 hε' hε'1 X Y hXm hYm hX hY
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let δ := max ε ε'
  have hδ : 0 < δ := hε.trans_le (le_max_left _ _)
  have hδ1 : δ ≤ 1 := max_le hε1 hε'1
  let F : UnitInterval → Ω → C(Torus3, ℝ) := fun u ω => X ω (((T + 2) * u - 1)) - Y ω (((T + 2) * u - 1))
  let Z : UnitInterval → Ω → HolderBesov η := fun u ω => toHolderBesov η (F u ω)
  have hXm' (u : ℝ) : Measurable (fun ω => X ω u) := (ContinuousMap.measurable_eval u).comp hXm
  have hYm' (u : ℝ) : Measurable (fun ω => Y ω u) := (ContinuousMap.measurable_eval u).comp hYm
  have hFm (u : UnitInterval) : Measurable (F u) :=
    measurable_spatial_sub (hXm' (((T + 2) * u - 1))) (hYm' (((T + 2) * u - 1)))
  have hedist (u v : UnitInterval) (ω : Ω) :
      edist (Z u ω) (Z v ω) = holderBesovENorm η (F u ω - F v ω) := by
    rw [edist_eq_enorm_sub, ← toHolderBesov_sub, enorm_toHolderBesov]
  have hZcont (ω : Ω) : Continuous (Z · ω) :=
    (toHolderBesov_lipschitzWith η).continuous.comp
      (((X ω).continuous.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)).sub
        ((Y ω).continuous.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)))
  have hZmeas (u v : UnitInterval) : AEMeasurable (fun ω => edist (Z u ω) (Z v ω)) P := by
    simp_rw [hedist]
    exact ((continuous_holderBesovENorm_negative η).measurable.comp
      (measurable_spatial_sub (hFm u) (hFm v))).aemeasurable
  have hpair (u v : UnitInterval) :
      (∫⁻ ω, edist (Z u ω) (Z v ω) ^ (2 * m) ∂P) ≤
        (ENNReal.ofReal (M * (T + 2) ^ q) * ENNReal.ofReal (δ ^ q)) * edist u v ^ q := by
    simp_rw [hedist]
    apply (hmix hW hε hε1 hε' hε'1 X Y hXm hYm hX hY (((T + 2) * u - 1)) (((T + 2) * v - 1))).trans_eq
    have he : |((T + 2) * (u : ℝ) - 1) - ((T + 2) * (v : ℝ) - 1)| =
        (T + 2) * |(u : ℝ) - v| := by
      have ha : ((T + 2) * (u : ℝ) - 1) - ((T + 2) * (v : ℝ) - 1) =
          (T + 2) * ((u : ℝ) - v) := by ring
      rw [ha, abs_mul, abs_of_pos hlen]
    rw [he, mul_rpow hlen.le (abs_nonneg _), edist_dist, Subtype.dist_eq, Real.dist_eq,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq,
      ← ENNReal.ofReal_mul (mul_nonneg hM (rpow_nonneg hlen.le _)),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hM (rpow_nonneg hlen.le _)) (rpow_nonneg hδ.le _))]
    congr 1
    ring
  have h0meas : AEMeasurable (fun ω => ‖Z 0 ω‖ₑ) P := by
    simp only [Z, enorm_toHolderBesov]
    exact ((continuous_holderBesovENorm_negative η).measurable.comp (hFm 0)).aemeasurable
  have hinit : (∫⁻ ω, ‖Z 0 ω‖ₑ ^ (2 * m) ∂P) ≤
      ENNReal.ofReal B * ENNReal.ofReal (δ ^ q) := by
    simp only [Z, enorm_toHolderBesov]
    apply (hscale hW hε hε1 hε' hε'1 (((T + 2) * (0 : UnitInterval) - 1))
      (fun ω => X ω (((T + 2) * (0 : UnitInterval) - 1))) (fun ω => Y ω (((T + 2) * (0 : UnitInterval) - 1)))
      (hXm' _) (hYm' _) (hX _) (hY _)).trans
    rw [← ENNReal.ofReal_mul hB]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hB
    exact rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [q]; linarith only [hmθ])
  have hs := hmax (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    Z hZcont hZmeas hpair h0meas hinit
  calc
    _ = ∫⁻ ω, (⨆ u : UnitInterval, ‖Z u ω‖ₑ) ^ (2 * m) ∂P := by
      simp only [Z, F, enorm_toHolderBesov]
    _ ≤ K * (ENNReal.ofReal B * ENNReal.ofReal (δ ^ q) +
        ENNReal.ofReal (M * (T + 2) ^ q) * ENNReal.ofReal (δ ^ q)) := hs
    _ = L * ENNReal.ofReal (δ ^ q) := by dsimp [L]; ring
    _ = ENNReal.ofReal (L.toReal * δ ^ q) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hL]
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]

end RegularityStructures.Phi43

end

