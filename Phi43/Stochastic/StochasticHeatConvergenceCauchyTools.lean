/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePathSup
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.CompletePartialOrder

/-!
# Moment interpolation and scale-preserving maximal bounds

These internal analytic inputs preserve a small parameter through a covariance increment
estimate and the Kolmogorov maximal estimate. In particular the maximal constant is chosen
before both the initial and increment moment constants.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures.Phi43

theorem lintegral_enorm_sub_natPow_le
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {P : Measure Ω}
    {U V : Ω → E} (hU : AEMeasurable (fun ω => ‖U ω‖ₑ) P)
    (hV : AEMeasurable (fun ω => ‖V ω‖ₑ) P) (p : ℕ) :
    (∫⁻ ω, ‖U ω - V ω‖ₑ ^ p ∂P) ≤
      (2 : ℝ≥0∞) ^ p * ((∫⁻ ω, ‖U ω‖ₑ ^ p ∂P) + ∫⁻ ω, ‖V ω‖ₑ ^ p ∂P) := by
  have hpoint (ω : Ω) : ‖U ω - V ω‖ₑ ^ p ≤
      (2 : ℝ≥0∞) ^ p * (‖U ω‖ₑ ^ p + ‖V ω‖ₑ ^ p) := by
    have hnorm : ‖U ω - V ω‖ₑ ≤ ‖U ω‖ₑ + ‖V ω‖ₑ := by
      simpa only [sub_eq_add_neg, enorm_neg] using enorm_add_le (U ω) (-V ω)
    apply (ENNReal.pow_le_pow_left hnorm).trans
    simpa only [ENNReal.rpow_natCast] using
      ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow ‖U ω‖ₑ ‖V ω‖ₑ (Nat.cast_nonneg p)
  calc
    _ ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ p * (‖U ω‖ₑ ^ p + ‖V ω‖ₑ ^ p) ∂P := lintegral_mono hpoint
    _ = _ := by
      have hsum : AEMeasurable (fun ω => ‖U ω‖ₑ ^ p + ‖V ω‖ₑ ^ p) P :=
        (hU.pow_const p).add (hV.pow_const p)
      rw [lintegral_const_mul'' _ hsum,
        lintegral_add_left' (hU.pow_const p)]

theorem ennreal_le_geometric_mean_of_two_bounds {a b c K : ℝ≥0∞}
    (hb : a ≤ K * b) (hc : a ≤ K * c) :
    a ≤ K * b ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) := by
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have he : (a * a) ^ (1 / 2 : ℝ) = a := by
    rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hroot := ENNReal.rpow_le_rpow (mul_le_mul' hb hc) hh
  rw [he] at hroot
  have hK : K ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) = K := by
    calc
      _ = K ^ ((1 / 2 : ℝ) + 1 / 2) := (ENNReal.rpow_add_of_nonneg _ _ hh hh).symm
      _ = K := by norm_num
  calc
    a ≤ ((K * b) * (K * c)) ^ (1 / 2 : ℝ) := hroot
    _ = (K ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ)) * b ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ hh]
      ring
    _ = _ := by rw [hK]

theorem continuous_process_sup_norm_moment_bound_scaled
    {p : ℕ} {q : ℝ} {r : ℝ≥0} (hp : 1 ≤ p) (hq : 0 ≤ q) (hr : 0 < r)
    (hpr : (p : ℝ) * (r : ℝ) < q - 1) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ {M B : ℝ≥0∞}, M ≠ ∞ →
      ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
      [CompleteSpace E] [T3Space E] {P : Measure Ω} (Z : UnitInterval → Ω → E),
      (∀ ω, Continuous (Z · ω)) →
      (∀ s t, AEMeasurable (fun ω => edist (Z s ω) (Z t ω)) P) →
      (∀ s t, ∫⁻ ω, edist (Z s ω) (Z t ω) ^ p ∂P ≤ M * edist s t ^ q) →
      AEMeasurable (fun ω => ‖Z 0 ω‖ₑ) P →
      (∫⁻ ω, ‖Z 0 ω‖ₑ ^ p ∂P ≤ B) →
      (∫⁻ ω, (⨆ t, ‖Z t ω‖ₑ) ^ p ∂P) ≤ K * (B + M) := by
  let L : ℝ≥0∞ := (1 + 2 * dyadicTailCoeff r) * (2 : ℝ≥0∞) ^ (r : ℝ)
  let S : ℝ≥0∞ := ∑' n : ℕ, (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1)
  let a : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((p : ℝ) - 1)
  let d : ℝ≥0∞ := L ^ p * ((10 : ℝ≥0∞) * (4 : ℝ≥0∞) ^ q * S)
  have hL : L ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp) (dyadicTailCoeff_lt_top hr).ne⟩)
    (ENNReal.rpow_lt_top_of_nonneg (show 0 ≤ (r : ℝ) from r.2) (by simp)).ne
  have hS : S ≠ ∞ := dyadicBase_rpow_tsum_ne_top (by linarith only [hpr])
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have ha : a ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hpR) (by simp)).ne
  have hd : d ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hL)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      (ENNReal.rpow_lt_top_of_nonneg hq (by simp)).ne) hS)
  refine ⟨a * (1 + d), ENNReal.mul_ne_top ha (ENNReal.add_ne_top.mpr ⟨by simp, hd⟩), ?_⟩
  intro M B hM Ω E _ _ _ _ P Z hcont hmeas hpair h0meas hinit
  obtain ⟨Y, hmatch, hholder, hsup⟩ := exists_kolmogorov_chentsov_sup_norm_moment
    hp hq hr hpr hM hmeas hpair h0meas hinit
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense UnitInterval
  let _ : Countable D := hDcount.to_subtype
  have hD : ∀ᵐ ω ∂P, ∀ t : D, Z t ω = Y t ω := ae_all_iff.mpr fun t => hmatch t
  have hall : ∀ᵐ ω ∂P, (fun t => Z t ω) = (fun t => Y t ω) := by
    filter_upwards [hD, hholder] with ω hω hω'
    exact hDdense.denseRange_val.equalizer (hcont ω) (hω'.continuous hr) (funext fun t => hω t)
  calc
    _ = ∫⁻ ω, (⨆ t, ‖Y t ω‖ₑ) ^ p ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hall] with ω hω
      simp_rw [congrFun hω]
    _ ≤ a * (B + L ^ p * ((10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q * S)) := hsup
    _ = a * (B + d * M) := by dsimp [d]; ring
    _ ≤ a * ((1 + d) * (B + M)) := by
      apply mul_le_mul_right
      calc
        B + d * M ≤ (B + d * M) + (M + d * B) := le_add_of_nonneg_right zero_le
        _ = _ := by ring
    _ = (a * (1 + d)) * (B + M) := by ring

theorem lintegral_rpow_le_of_scaled_natMoment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ≥0∞} {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hpn : p ≤ n)
    {b C : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ∞)
    (hbound : (∫⁻ ω, f ω ^ n ∂P) ≤ C * b ^ n) :
    (∫⁻ ω, f ω ^ p ∂P) ≤ (1 + C) * b ^ p := by
  let g : Ω → ℝ≥0∞ := fun ω => b⁻¹ * f ω
  have hbinv : b⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hb0
  have hbpow : b ^ p ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg hp hbtop).ne
  have hg : (∫⁻ ω, g ω ^ n ∂P) ≤ C := by
    calc
      _ = (b⁻¹) ^ n * ∫⁻ ω, f ω ^ n ∂P := by
        simp only [g, mul_pow]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top hbinv)
      _ ≤ (b⁻¹) ^ n * (C * b ^ n) := mul_le_mul_right hbound _
      _ = C := by
        rw [show (b⁻¹) ^ n * (C * b ^ n) = C * ((b⁻¹) ^ n * b ^ n) by ring,
          ← mul_pow, ENNReal.inv_mul_cancel hb0 hbtop, one_pow, mul_one]
  have hpoint (a : ℝ≥0∞) : a ^ p ≤ 1 + a ^ n := by
    by_cases ha : a ≤ 1
    · exact (ENNReal.rpow_le_one ha hp).trans (le_add_of_nonneg_right zero_le)
    · have hpow := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge ha) hpn
      rw [ENNReal.rpow_natCast] at hpow
      exact hpow.trans (le_add_of_nonneg_left zero_le)
  have hgp : (∫⁻ ω, g ω ^ p ∂P) ≤ 1 + C := by
    calc
      _ ≤ ∫⁻ ω, 1 + g ω ^ n ∂P := lintegral_mono fun ω => hpoint _
      _ = 1 + ∫⁻ ω, g ω ^ n ∂P := by
        rw [lintegral_add_left measurable_const]
        simp only [lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + C := add_le_add_right hg _
  have he (ω : Ω) : f ω = b * g ω := by
    dsimp [g]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hb0 hbtop, one_mul]
  calc
    _ = ∫⁻ ω, b ^ p * g ω ^ p ∂P := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact (congrArg (fun a : ℝ≥0∞ => a ^ p) (he ω)).trans
        (ENNReal.mul_rpow_of_nonneg _ _ hp)
    _ = b ^ p * ∫⁻ ω, g ω ^ p ∂P := lintegral_const_mul' _ _ hbpow
    _ ≤ b ^ p * (1 + C) := mul_le_mul_right hgp _
    _ = (1 + C) * b ^ p := mul_comm _ _

end RegularityStructures.Phi43

end
