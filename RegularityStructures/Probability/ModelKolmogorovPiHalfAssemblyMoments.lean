/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGlobalSourceMoments

/-!
# Moment lemmas for the `Π` half assembly

Elementary `ℝ≥0∞` moment facts: `(x + y)^m ≤ 2^m (x^m + y^m)`, Lyapunov monotonicity of moments
for `ℝ≥0∞`-valued variables, the union bound for a countable supremum, and the Cauchy–Schwarz
bound `E[f g] ≤ √(E f²) √(E g²)`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem ennreal_add_pow_le (x y : ℝ≥0∞) (m : ℕ) : (x + y) ^ m ≤ 2 ^ m * (x ^ m + y ^ m) := by
  have h : x + y ≤ 2 * max x y := by
    rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  calc (x + y) ^ m ≤ (2 * max x y) ^ m := pow_le_pow_left' h m
    _ = 2 ^ m * max x y ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (x ^ m + y ^ m) := by
      gcongr
      rcases le_total x y with hxy | hxy
      · rw [max_eq_right hxy]; exact le_add_self
      · rw [max_eq_left hxy]; exact le_self_add

/-- Lyapunov monotonicity of moments for `ℝ≥0∞`-valued random variables. -/
theorem lintegral_pow_le_of_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ≥0∞} (hY : AEMeasurable Y P) {p q : ℕ} (hp : 1 ≤ p)
    (hpq : p ≤ q) {b : ℝ} (h : ∫⁻ ω, Y ω ^ q ∂P ≤ ENNReal.ofReal b ^ q) :
    ∫⁻ ω, Y ω ^ p ∂P ≤ ENNReal.ofReal b ^ p := by
  have hq0 : q ≠ 0 := by omega
  have hfin : ∫⁻ ω, Y ω ^ q ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) h
  have hae : ∀ᵐ ω ∂P, Y ω < ⊤ := by
    filter_upwards [ae_lt_top' (hY.pow_const q) hfin] with ω hω
    exact lt_top_iff_ne_top.2 fun h' => hω.ne (by simp [h', hq0])
  have hf : AEMeasurable (fun ω => (Y ω).toReal) P := hY.ennreal_toReal
  have hnorm : ∀ᵐ ω ∂P, ‖(Y ω).toReal‖ₑ = Y ω := by
    filter_upwards [hae] with ω hω
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hω.ne]
  have h' : ∫⁻ ω, ‖(Y ω).toReal‖ₑ ^ q ∂P ≤ ENNReal.ofReal b ^ q := by
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) h
    filter_upwards [hnorm] with ω hω using by rw [hω]
  have := probability_natMoment_le_of_higher hf hp hpq _ h'
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) this
  filter_upwards [hnorm] with ω hω using by rw [hω]

/-- Pointwise: the `m`-th power of a supremum is at most the sum of the `m`-th powers. -/
theorem iSup_pow_le_tsum {σ : Type*} (f : σ → ℝ≥0∞) {m : ℕ} (hm : m ≠ 0) :
    (⨆ x, f x) ^ m ≤ ∑' x, f x ^ m := by
  rw [ENNReal.iSup_pow_of_ne_zero hm]
  exact iSup_le fun x => ENNReal.le_tsum (f := fun y => f y ^ m) x

/-- Union bound for a countable supremum. -/
theorem lintegral_iSup_pow_le_tsum {Ω σ : Type*} [MeasurableSpace Ω] [Countable σ]
    {P : Measure Ω} {f : σ → Ω → ℝ≥0∞} (hf : ∀ x, AEMeasurable (f x) P) {m : ℕ}
    (hm : m ≠ 0) :
    ∫⁻ ω, (⨆ x, f x ω) ^ m ∂P ≤ ∑' x, ∫⁻ ω, f x ω ^ m ∂P := by
  calc ∫⁻ ω, (⨆ x, f x ω) ^ m ∂P ≤ ∫⁻ ω, ∑' x, f x ω ^ m ∂P :=
        lintegral_mono fun ω => iSup_pow_le_tsum (fun x => f x ω) hm
    _ = ∑' x, ∫⁻ ω, f x ω ^ m ∂P := lintegral_tsum fun x => (hf x).pow_const m

/-- Cauchy–Schwarz for `ℝ≥0∞`-valued functions. -/
theorem lintegral_mul_le_sqrt_mul_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f P) (hg : AEMeasurable g P) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hfa : ∫⁻ ω, f ω ^ 2 ∂P ≤ ENNReal.ofReal a)
    (hgb : ∫⁻ ω, g ω ^ 2 ∂P ≤ ENNReal.ofReal b) :
    ∫⁻ ω, f ω * g ω ∂P ≤ ENNReal.ofReal (Real.sqrt a * Real.sqrt b) := by
  have hc : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hc hf hg
  simp only [ENNReal.rpow_two, Pi.mul_apply] at h
  refine h.trans ?_
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg ha (by norm_num),
    ← ENNReal.ofReal_rpow_of_nonneg hb (by norm_num)]
  gcongr

end RegularityStructures

end
