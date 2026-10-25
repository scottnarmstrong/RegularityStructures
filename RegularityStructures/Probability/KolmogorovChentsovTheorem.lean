/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovPath
public import RegularityStructures.Probability.KolmogorovChentsovPointwise
public import RegularityStructures.Probability.KolmogorovChentsovExtension

/-!
# The Kolmogorov--Chentsov modification theorem

This is the complete-metric-space theorem on the unit interval.  If the
pairwise `p`-moment is bounded by `M * edist s t ^ q`, then every exponent
`r > 0` with `p * r < q - 1` has a Hölder modification.  All random bounds
are stated with `lintegral`; in particular, the proof does not assume a
Bochner integrability hypothesis hidden in the conclusion.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem exists_kolmogorov_chentsov_modification
    {Ω E : Type*} [MeasurableSpace Ω] [EMetricSpace E] [CompleteSpace E]
    [T3Space E] {P : Measure Ω} {X : UnitInterval → Ω → E}
    {p : ℕ} {q : ℝ} {M : ℝ≥0∞} {r : ℝ≥0}
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hr : 0 < r)
    (hpr : (p : ℝ) * (r : ℝ) < q - 1) (hM : M ≠ ∞)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (X s ω) (X t ω)) P)
    (hpair : ∀ s t, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤
      M * edist s t ^ q) :
    ∃ Y : UnitInterval → Ω → E,
      (∀ t, X t =ᵐ[P] Y t) ∧
      (∀ᵐ ω ∂P, HolderWith
        (dyadicNormalisedSup X r ω *
          (1 + 2 * dyadicTailCoeff r) * (2 : ℝ≥0∞) ^ (r : ℝ)).toNNReal
        r (Y · ω)) ∧
      (∫⁻ ω, eHolderNorm r (Y · ω) ^ p ∂P ≤
        ((1 + 2 * dyadicTailCoeff r) * (2 : ℝ≥0∞) ^ (r : ℝ)) ^ p *
          ((10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
            ∑' n : ℕ, (dyadicBase n) ^
              (q - (p : ℝ) * (r : ℝ) - 1))) := by
  have hp0 : p ≠ 0 := by omega
  have hfinite := dyadicNormalisedSup_lintegral_pow_lt_top
    hp hq hr.le hpr hM X
      (P := P) hmeas hpair
  have hSbound := dyadicNormalisedSup_lintegral_pow_le
    hp hq hr.le hpr X (P := P) hmeas hpair
  have hSmeas := dyadicNormalisedSup_aemeasurable X r (P := P) hmeas
  have hSae_pow : ∀ᵐ ω ∂P, dyadicNormalisedSup X r ω ^ p < ∞ :=
    ae_lt_top' (hSmeas.pow_const p) hfinite.ne
  have hSae : ∀ᵐ ω ∂P, dyadicNormalisedSup X r ω < ∞ := by
    filter_upwards [hSae_pow] with ω hω
    exact (ENNReal.pow_lt_top_iff.mp hω).resolve_right hp0
  let K : ℝ≥0∞ := (1 + 2 * dyadicTailCoeff r) *
    (2 : ℝ≥0∞) ^ (r : ℝ)
  have hK : K ≠ ∞ := by
    dsimp [K]
    apply ENNReal.mul_ne_top
    · have htwo : (2 : ℝ≥0∞) * dyadicTailCoeff r ≠ ∞ :=
        ENNReal.mul_ne_top (by simp) (dyadicTailCoeff_lt_top hr).ne
      exact (ENNReal.add_ne_top).2 ⟨by simp, htwo⟩
    · have hpow : (2 : ℝ≥0∞) ^ (r : ℝ) < ∞ :=
        ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)
      exact hpow.ne
  let C : Ω → ℝ≥0 := fun ω =>
    (dyadicNormalisedSup X r ω * K).toNNReal
  have hpath : ∀ᵐ ω ∂P, HolderWith (C ω) r
      (fun x : dyadicUnitSet => X x ω) := by
    filter_upwards [hSae] with ω hω
    have hω' := holderOnWith_of_dyadicNormalisedSup_lt_top
      (X := X) hr hω
    simpa [C, K, mul_assoc] using holderOnWith_subtype hω'
  let Y : UnitInterval → Ω → E := fun t ω =>
    dense_dyadicUnitSet.extend (fun x : dyadicUnitSet => X x ω) t
  have hqpos : 0 < q := by
    have hnonneg : 0 ≤ (p : ℝ) * (r : ℝ) :=
      mul_nonneg (by positivity) hr.le
    linarith
  have hmatch : ∀ t, ∀ᵐ ω ∂P, X t ω = Y t ω := by
    intro t
    have hpoint := ae_tendsto_dyadicApprox_of_moment_bound
      hp hqpos hM t (P := P) hmeas hpair
    filter_upwards [hpath, hpoint] with ω hω hωpoint
    have hbase : Tendsto (fun n : ℕ => dyadicBase n) atTop
        (𝓝 (0 : ℝ≥0∞)) := by
      change Tendsto (fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ n) atTop
        (𝓝 (0 : ℝ≥0∞))
      apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      norm_num
    have happrox_edist : ∀ n,
        edist (dyadicApprox n t) t ≤ dyadicBase n := by
      intro n
      rw [← ofReal_inv_two_pow n]
      simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, dist_comm] using
        edist_dyadicApprox_le n t
    have happrox_edist_zero : Tendsto
        (fun n => edist (dyadicApprox n t) t) atTop
          (𝓝 (0 : ℝ≥0∞)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hbase (fun _ => bot_le) happrox_edist
    have happrox : Tendsto (fun n => (dyadicApprox n t : UnitInterval)) atTop
        (𝓝 t) := by
      simpa only [tendsto_iff_edist_tendsto_0] using happrox_edist_zero
    have hsub : Tendsto
        (fun n => (⟨dyadicApprox n t, dyadicApprox_mem n t⟩ : dyadicUnitSet))
        atTop (comap (↑) (𝓝 t)) := by
      rw [tendsto_comap_iff]
      simpa [Function.comp_def] using happrox
    have hext := dense_holder_extension_tendsto dense_dyadicUnitSet hω hr t
    have hY : Tendsto (fun n => X (dyadicApprox n t) ω) atTop
        (𝓝 (Y t ω)) := by
      simpa [Y, Function.comp_def] using hext.comp hsub
    exact tendsto_nhds_unique hωpoint hY
  have hYholder : ∀ᵐ ω ∂P, HolderWith (C ω) r (Y · ω) := by
    filter_upwards [hpath] with ω hω
    simpa [Y] using dense_holderWith_extend dense_dyadicUnitSet hω hr
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro t
    exact hmatch t
  · simpa [C, K, mul_assoc] using hYholder
  · have hbound : ∀ᵐ ω ∂P,
        eHolderNorm r (Y · ω) ^ p ≤
          (dyadicNormalisedSup X r ω * K) ^ p := by
      filter_upwards [hSae, hYholder] with ω hω hYω
      have hSK : dyadicNormalisedSup X r ω * K ≠ ∞ :=
        ENNReal.mul_ne_top hω.ne hK
      have hC : (C ω : ℝ≥0∞) = dyadicNormalisedSup X r ω * K := by
        exact ENNReal.coe_toNNReal hSK
      calc
        eHolderNorm r (Y · ω) ^ p ≤ (C ω : ℝ≥0∞) ^ p := by
          gcongr
          exact hYω.eHolderNorm_le
        _ = (dyadicNormalisedSup X r ω * K) ^ p := by rw [hC]
    calc
      ∫⁻ ω, eHolderNorm r (Y · ω) ^ p ∂P ≤
          ∫⁻ ω, (dyadicNormalisedSup X r ω * K) ^ p ∂P :=
        lintegral_mono_ae hbound
      _ = K ^ p * ∫⁻ ω, dyadicNormalisedSup X r ω ^ p ∂P := by
        calc
          ∫⁻ ω, (dyadicNormalisedSup X r ω * K) ^ p ∂P =
              (∫⁻ ω, dyadicNormalisedSup X r ω ^ p ∂P) * K ^ p := by
            simp_rw [mul_pow]
            rw [lintegral_mul_const'' _ (hSmeas.pow_const p)]
          _ = K ^ p * ∫⁻ ω, dyadicNormalisedSup X r ω ^ p ∂P := by
            ring
      _ ≤ K ^ p * ((10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
          ∑' n : ℕ, (dyadicBase n) ^
            (q - (p : ℝ) * (r : ℝ) - 1)) := by
        gcongr
      _ = ((1 + 2 * dyadicTailCoeff r) * (2 : ℝ≥0∞) ^ (r : ℝ)) ^ p *
          ((10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
            ∑' n : ℕ, (dyadicBase n) ^
              (q - (p : ℝ) * (r : ℝ) - 1)) := by
        rfl

end RegularityStructures

end
