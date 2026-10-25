/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentChain
import Mathlib.Tactic

/-!
# `q`-th moments of a Taylor-remainder cocycle at all distances

From local `q`-th moment bounds (`d ≤ 1/2`) of `v` and of the additive `γ` and the cocycle relation
one gets the bound `ofReal ((B + 128 A) (d^s + d^4))^q` for all pairs
(`lintegral_enorm_nearFar_pow_le`), `d = ‖y - x‖_𝔰`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

/-- For a measurable function, the `q`-th moment bound is the `L^q` norm bound. -/
theorem lintegral_enorm_pow_le_iff_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) {q : ℕ} (hq : 1 ≤ q) {B : ℝ≥0∞} :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ B ^ q ↔ eLpNorm f (q : ℝ≥0∞) P ≤ B := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have h0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : (q : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top q
  rw [eLpNorm_eq_eLpNorm' h0 h1 hf.aestronglyMeasurable, ENNReal.toReal_natCast]
  have := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f) (μ := P) hqpos
  simp only [ENNReal.rpow_natCast] at this
  rw [this, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ENNReal.rpow_le_rpow_iff hqpos]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **`q`-th moments of a Taylor-remainder cocycle at all distances.** -/
theorem lintegral_enorm_nearFar_pow_le {q : ℕ} (hq : 1 ≤ q) {B B' s : ℝ} (hB : 0 ≤ B)
    (hs : 0 ≤ s)
    (v : ParabolicSpace → ParabolicSpace → Ω → ℝ)
    (γ : Fin 3 → ParabolicSpace → ParabolicSpace → Ω → ℝ)
    (hvm : ∀ x y, Measurable (v x y)) (hγm : ∀ i x y, Measurable (γ i x y))
    (hcoc : ∀ x z y ω, v x y ω = v x z ω + v z y ω + ∑ i, γ i x z ω * (y.2 i - z.2 i))
    (hadd : ∀ i x z y ω, γ i x y ω = γ i x z ω + γ i z y ω)
    (hnv : ∀ x y, parabolicNorm (y - x) ≤ 1 / 2 →
      ∫⁻ ω, ‖v x y ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (B * parabolicNorm (y - x) ^ s) ^ q)
    (hnγ : ∀ i x y, parabolicNorm (y - x) ≤ 1 / 2 →
      ∫⁻ ω, ‖γ i x y ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal B' ^ q) (x y : ParabolicSpace) :
    ∫⁻ ω, ‖v x y ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal ((B + 128 * max B B') *
        (parabolicNorm (y - x) ^ s + parabolicNorm (y - x) ^ (4 : ℕ))) ^ q := by
  have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  have hs0 : 0 ≤ parabolicNorm (y - x) ^ s := Real.rpow_nonneg hd0 _
  have h40 : 0 ≤ parabolicNorm (y - x) ^ (4 : ℕ) := pow_nonneg hd0 _
  have hmax : 0 ≤ max B B' := le_max_of_le_left hB
  by_cases hnear : parabolicNorm (y - x) ≤ 1 / 2
  · refine (hnv x y hnear).trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
    have : B ≤ B + 128 * max B B' := by linarith
    calc B * parabolicNorm (y - x) ^ s ≤ (B + 128 * max B B') * parabolicNorm (y - x) ^ s :=
          mul_le_mul_of_nonneg_right this hs0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hfar := lt_of_not_ge hnear
    have hA : 0 ≤ max B B' := hmax
    have hqe : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hq
    have hnv' : ∀ x y, parabolicNorm (y - x) ≤ 1 / 2 →
        eLpNorm (v x y) (q : ℝ≥0∞) P ≤ ENNReal.ofReal (max B B') := by
      intro x y h
      have h1 := (lintegral_enorm_pow_le_iff_eLpNorm_le (hvm x y) hq).1 (hnv x y h)
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      have hd1 : parabolicNorm (y - x) ≤ 1 := by linarith
      have : parabolicNorm (y - x) ^ s ≤ 1 :=
        Real.rpow_le_one (parabolicNorm_nonneg _) hd1 hs
      calc B * parabolicNorm (y - x) ^ s ≤ B * 1 := mul_le_mul_of_nonneg_left this hB
        _ ≤ max B B' := by rw [mul_one]; exact le_max_left _ _
    have hnγ' : ∀ i x y, parabolicNorm (y - x) ≤ 1 / 2 →
        eLpNorm (γ i x y) (q : ℝ≥0∞) P ≤ ENNReal.ofReal (max B B') := by
      intro i x y h
      have h1 := (lintegral_enorm_pow_le_iff_eLpNorm_le (hγm i x y) hq).1 (hnγ i x y h)
      exact h1.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    have hf := eLpNorm_far_le hqe hA v γ hcoc hadd hnv' hnγ' x y hfar
    have h2 := (lintegral_enorm_pow_le_iff_eLpNorm_le (hvm x y) hq).2 hf
    refine h2.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
    have h3 : 128 * max B B' ≤ B + 128 * max B B' := by linarith
    calc 128 * max B B' * parabolicNorm (y - x) ^ 4
        ≤ (B + 128 * max B B') * parabolicNorm (y - x) ^ 4 :=
          mul_le_mul_of_nonneg_right h3 h40
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end RegularityStructures

end
