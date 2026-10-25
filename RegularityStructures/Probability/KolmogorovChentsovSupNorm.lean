/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovTheorem
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Order.CompletePartialOrder

/-!
# Supremum moments for norm-valued Kolmogorov modifications

For a normed complete target, a Hölder modification is bounded by its value at
time zero and its Hölder seminorm.  This gives the usual moment estimate for
the supremum over the unit interval.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem exists_kolmogorov_chentsov_sup_norm_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [CompleteSpace E] [T3Space E] {P : Measure Ω}
    {Z : UnitInterval → Ω → E} {p : ℕ} {q : ℝ} {M B : ℝ≥0∞}
    {r : ℝ≥0} (hp : 1 ≤ p) (hq : 0 ≤ q) (hr : 0 < r)
    (hpr : (p : ℝ) * (r : ℝ) < q - 1) (hM : M ≠ ∞)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (Z s ω) (Z t ω)) P)
    (hpair : ∀ s t, ∫⁻ ω, edist (Z s ω) (Z t ω) ^ p ∂P ≤
      M * edist s t ^ q)
    (h0meas : AEMeasurable (fun ω => ‖Z 0 ω‖ₑ) P)
    (hinit : ∫⁻ ω, ‖Z 0 ω‖ₑ ^ p ∂P ≤ B) :
    ∃ Y : UnitInterval → Ω → E,
      (∀ t, Z t =ᵐ[P] Y t) ∧
      (∀ᵐ ω ∂P, HolderWith
        (dyadicNormalisedSup Z r ω *
          (1 + 2 * dyadicTailCoeff r) * (2 : ℝ≥0∞) ^ (r : ℝ)).toNNReal
        r (Y · ω)) ∧
      (∫⁻ ω, (⨆ t, ‖Y t ω‖ₑ) ^ p ∂P ≤
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (B + ((1 + 2 * dyadicTailCoeff r) *
            (2 : ℝ≥0∞) ^ (r : ℝ)) ^ p *
            ((10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
              ∑' n : ℕ, (dyadicBase n) ^
                (q - (p : ℝ) * (r : ℝ) - 1)))) := by
  obtain ⟨Y, hmatch, hholder, _hmoment⟩ :=
    exists_kolmogorov_chentsov_modification hp hq hr hpr hM
      hmeas hpair
  have hp0 : p ≠ 0 := by omega
  have hfinite := dyadicNormalisedSup_lintegral_pow_lt_top
    hp hq hr.le hpr hM Z (P := P) hmeas hpair
  have hSbound := dyadicNormalisedSup_lintegral_pow_le
    hp hq hr.le hpr Z (P := P) hmeas hpair
  have hSmeas := dyadicNormalisedSup_aemeasurable Z r (P := P) hmeas
  have hSae_pow : ∀ᵐ ω ∂P, dyadicNormalisedSup Z r ω ^ p < ∞ :=
    ae_lt_top' (hSmeas.pow_const p) hfinite.ne
  have hSae : ∀ᵐ ω ∂P, dyadicNormalisedSup Z r ω < ∞ := by
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
    (dyadicNormalisedSup Z r ω * K).toNNReal
  have hCmeas : AEMeasurable (fun ω => (C ω : ℝ≥0∞)) P := by
    simpa [C] using
      (hSmeas.mul_const K).ennreal_toNNReal.coe_nnreal_ennreal
  have hholder' : ∀ᵐ ω ∂P, HolderWith (C ω) r (Y · ω) := by
    filter_upwards [hholder] with ω hω
    simpa [C, K, mul_assoc] using hω
  have hCmoment : ∫⁻ ω, (C ω : ℝ≥0∞) ^ p ∂P =
      K ^ p * ∫⁻ ω, dyadicNormalisedSup Z r ω ^ p ∂P := by
    have hCeq : ∀ᵐ ω ∂P, (C ω : ℝ≥0∞) ^ p =
        (dyadicNormalisedSup Z r ω * K) ^ p := by
      filter_upwards [hSae] with ω hω
      have hSK : dyadicNormalisedSup Z r ω * K ≠ ∞ :=
        ENNReal.mul_ne_top hω.ne hK
      rw [show (C ω : ℝ≥0∞) = dyadicNormalisedSup Z r ω * K by
        exact ENNReal.coe_toNNReal hSK]
    calc
      ∫⁻ ω, (C ω : ℝ≥0∞) ^ p ∂P =
          ∫⁻ ω, (dyadicNormalisedSup Z r ω * K) ^ p ∂P :=
        lintegral_congr_ae hCeq
      _ = (∫⁻ ω, dyadicNormalisedSup Z r ω ^ p ∂P) * K ^ p := by
        simp_rw [mul_pow]
        rw [lintegral_mul_const'' _ (hSmeas.pow_const p)]
      _ = K ^ p * ∫⁻ ω, dyadicNormalisedSup Z r ω ^ p ∂P := by
        ring
  have hsup : ∀ᵐ ω ∂P,
      (⨆ t, ‖Y t ω‖ₑ) ≤ ‖Z 0 ω‖ₑ + (C ω : ℝ≥0∞) := by
    filter_upwards [hmatch 0, hholder'] with ω hzero hω
    apply iSup_le
    intro t
    have hpow : edist t (0 : UnitInterval) ^ (r : ℝ) ≤ 1 :=
      ENNReal.rpow_le_one (edist_unitInterval_le_one t 0) hr.le
    calc
      ‖Y t ω‖ₑ = edist (Y t ω) 0 := by simp
      _ ≤ edist (Y t ω) (Y 0 ω) + edist (Y 0 ω) 0 :=
        edist_triangle _ _ _
      _ ≤ (C ω : ℝ≥0∞) * edist t 0 ^ (r : ℝ) +
          ‖Y 0 ω‖ₑ := by
        exact add_le_add (hω t 0) (by simp [edist_eq_enorm_sub])
      _ ≤ (C ω : ℝ≥0∞) + ‖Y 0 ω‖ₑ := by
        calc
          (C ω : ℝ≥0∞) * edist t 0 ^ (r : ℝ) + ‖Y 0 ω‖ₑ ≤
              (C ω : ℝ≥0∞) * 1 + ‖Y 0 ω‖ₑ :=
            by
              exact add_le_add
                (by simpa [mul_comm] using
                  mul_le_mul_left hpow (C ω : ℝ≥0∞))
                (le_refl _)
          _ = (C ω : ℝ≥0∞) + ‖Y 0 ω‖ₑ := by simp
      _ = ‖Z 0 ω‖ₑ + (C ω : ℝ≥0∞) := by
        rw [hzero]
        ring
  have hpoint : ∀ᵐ ω ∂P,
      (⨆ t, ‖Y t ω‖ₑ) ^ p ≤
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (‖Z 0 ω‖ₑ ^ p + (C ω : ℝ≥0∞) ^ p) := by
    filter_upwards [hsup] with ω hω
    calc
      (⨆ t, ‖Y t ω‖ₑ) ^ p ≤
          (‖Z 0 ω‖ₑ + (C ω : ℝ≥0∞)) ^ p :=
        ENNReal.pow_le_pow_left hω
      _ = (‖Z 0 ω‖ₑ + (C ω : ℝ≥0∞)) ^ (p : ℝ) := by
        rw [ENNReal.rpow_natCast]
      _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (‖Z 0 ω‖ₑ ^ (p : ℝ) + (C ω : ℝ≥0∞) ^ (p : ℝ)) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by exact_mod_cast hp)
      _ = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (‖Z 0 ω‖ₑ ^ p + (C ω : ℝ≥0∞) ^ p) := by
        rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast]
  have hsum : ∫⁻ ω, (⨆ t, ‖Y t ω‖ₑ) ^ p ∂P ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (∫⁻ ω, ‖Z 0 ω‖ₑ ^ p ∂P +
          ∫⁻ ω, (C ω : ℝ≥0∞) ^ p ∂P) := by
    calc
      ∫⁻ ω, (⨆ t, ‖Y t ω‖ₑ) ^ p ∂P ≤
          ∫⁻ ω, (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
            (‖Z 0 ω‖ₑ ^ p + (C ω : ℝ≥0∞) ^ p) ∂P :=
        lintegral_mono_ae hpoint
      _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          ∫⁻ ω, (‖Z 0 ω‖ₑ ^ p + (C ω : ℝ≥0∞) ^ p) ∂P :=
        (lintegral_const_mul'' _
          ((h0meas.pow_const p).add (hCmeas.pow_const p))).le
      _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (∫⁻ ω, ‖Z 0 ω‖ₑ ^ p ∂P +
            ∫⁻ ω, (C ω : ℝ≥0∞) ^ p ∂P) := by
        rw [lintegral_add_left' (h0meas.pow_const p)]
  refine ⟨Y, hmatch, ?_, ?_⟩
  · simpa [C, K, mul_assoc] using hholder'
  · calc
      ∫⁻ ω, (⨆ t, ‖Y t ω‖ₑ) ^ p ∂P ≤
          (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
            (∫⁻ ω, ‖Z 0 ω‖ₑ ^ p ∂P +
              ∫⁻ ω, (C ω : ℝ≥0∞) ^ p ∂P) := hsum
      _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (B + K ^ p * ∫⁻ ω, dyadicNormalisedSup Z r ω ^ p ∂P) := by
        gcongr
        exact le_of_eq hCmoment
      _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (B + K ^ p * ((10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
            ∑' n : ℕ, (dyadicBase n) ^
              (q - (p : ℝ) * (r : ℝ) - 1))) := by
        gcongr
      _ = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (B + ((1 + 2 * dyadicTailCoeff r) *
            (2 : ℝ≥0∞) ^ (r : ℝ)) ^ p *
            ((10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
              ∑' n : ℕ, (dyadicBase n) ^
                (q - (p : ℝ) * (r : ℝ) - 1))) := by
        rfl

end RegularityStructures

end
