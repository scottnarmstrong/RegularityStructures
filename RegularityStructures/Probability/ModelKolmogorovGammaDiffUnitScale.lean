/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffUnitGood
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffScale
import Mathlib.Tactic.Linarith

/-!
# Finite uniform scale constants for the source-free near good bounds

For the source-free near good bounds `gammaDiffNear{Left,Right}GoodBound 𝒯 D κ 1 C̄ 1 m`, on the
annular configurations of the unit-box telescope (coarse distance `≤ 24 · 2^{-N}`, fine distance
`≤ 4 · 2^{-(N+l)}`) the bound is at most `L (2^{-N})^{m(β+ρ)} (2^{-l})^{mρ}` with an explicit finite
constant `L`, for any `ρ` below `κ` and below every positive degree gap.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem gammaDiffUnitScale_base_le_one (n : ℕ) : dyadicBase n ≤ 1 := by
  unfold dyadicBase
  exact pow_le_one₀ (by positivity) (by norm_num)

private theorem gammaDiffUnitScale_term_le {K d e a b β ρ : ℝ} {m N l : ℕ} (hK : 0 ≤ K)
    (hd : 0 ≤ d) (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : β + ρ ≤ a + b)
    (hbρ : ρ ≤ b) (hd' : d ≤ 24 / (2 : ℝ) ^ N) (he' : e ≤ 4 / (2 : ℝ) ^ (N + l)) :
    ENNReal.ofReal (K * (d ^ a * e ^ b)) ^ m ≤
      (dyadicBase N ^ ((m : ℝ) * (β + ρ)) * dyadicBase l ^ ((m : ℝ) * ρ)) *
        ENNReal.ofReal (K * (24 : ℝ) ^ a * 4 ^ b) ^ m := by
  have h := gammaDiffOfRealProductScale_le (C := K) (A := 24) (B := 4) (q := m) (N := N)
    (l := l) hK (by norm_num) (by norm_num) hd he ha hb (by rw [mul_one_div]; exact hd')
    (by rw [mul_one_div]; exact he')
  have hN : dyadicBase N ^ ((m : ℝ) * (a + b)) ≤ dyadicBase N ^ ((m : ℝ) * (β + ρ)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge (gammaDiffUnitScale_base_le_one N)
      (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg m))
  have hl : dyadicBase l ^ ((m : ℝ) * b) ≤ dyadicBase l ^ ((m : ℝ) * ρ) :=
    ENNReal.rpow_le_rpow_of_exponent_ge (gammaDiffUnitScale_base_le_one l)
      (mul_le_mul_of_nonneg_left hbρ (Nat.cast_nonneg m))
  rw [show K * (d ^ a * e ^ b) = K * d ^ a * e ^ b by ring]
  calc
    _ ≤ _ := h
    _ ≤ ENNReal.ofReal (K * (24 : ℝ) ^ a * 4 ^ b) ^ m *
        dyadicBase N ^ ((m : ℝ) * (β + ρ)) * dyadicBase l ^ ((m : ℝ) * ρ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hN (by positivity)) hl (by positivity)
        (by positivity)
    _ = _ := by ring

private theorem gammaDiffUnitScale_mem_good {𝒯 : RegularityStructure ι} {D : Set (ι × ι)}
    {i j k : ι} (hk : k ∈ gammaGoodIntermediate 𝒯 D i j) :
    𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i ∧ ¬((i, k) ∈ D ∧ (k, j) ∈ D) := by
  classical
  have h := Finset.mem_filter.mp hk
  have h' := Finset.mem_filter.mp h.1
  exact ⟨h'.2.1, h'.2.2, h.2⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem gammaDiffUnitScale_card_ne_top (s : Finset ι) {m : ℕ} (hm : 1 ≤ m) :
    (s.card : ℝ≥0∞) ^ ((m : ℝ) - 1) ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith) (ENNReal.natCast_ne_top _)

/-- **Finite uniform scale constant for the left source-free near good bound.** -/
theorem gammaDiffNearLeftGoodBound_finite_scale
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι)) (κ Cbar ρ : ℝ) {m : ℕ} (i j : ι)
    (hm : 1 ≤ m) (hCbar : 0 ≤ Cbar) (hκ : 0 < κ) (hρκ : ρ < κ)
    (hρgap : ∀ a b : ι, 𝒯.deg b < 𝒯.deg a → ρ < 𝒯.deg a - 𝒯.deg b)
    (hj : 𝒯.deg j < 𝒯.deg i) (hij : (i, j) ∉ D) :
    ∃ L : ℝ≥0∞, L ≠ ∞ ∧ ∀ (N l : ℕ) (x y z : ParabolicSpace),
      parabolicSemigroup.scaleDist y x ≤ 24 / (2 : ℝ) ^ N →
      parabolicSemigroup.scaleDist z y ≤ 4 / (2 : ℝ) ^ (N + l) →
      gammaDiffNearLeftGoodBound 𝒯 D κ 1 Cbar 1 m i j x y z ≤
        L * dyadicBase N ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + ρ)) *
          dyadicBase l ^ ((m : ℝ) * ρ) := by
  classical
  let s := gammaGoodIntermediate 𝒯 D i j
  let eL : ι → ℝ := fun k => 𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)
  let eR : ι → ℝ := fun k => 𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)
  let e0 : ℝ := 𝒯.deg i - 𝒯.deg j + (if (i, j) ∈ D then 0 else κ)
  let A' : ℝ≥0∞ := ENNReal.ofReal (1 * (24 : ℝ) ^ (0 : ℝ) * 4 ^ e0) ^ m
  let B' : ι → ℝ≥0∞ := fun k => ENNReal.ofReal (Cbar * (24 : ℝ) ^ eL k * 4 ^ eR k) ^ m
  let c : ℝ≥0∞ := (s.card : ℝ≥0∞) ^ ((m : ℝ) - 1)
  let d : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((m : ℝ) - 1)
  have hc : c ≠ ∞ := gammaDiffUnitScale_card_ne_top s hm
  refine ⟨d * (A' + c * d * ∑ k ∈ s, (B' k + B' k)), ?_, ?_⟩
  · have hd : d ≠ ∞ := by finiteness
    have hA' : A' ≠ ∞ := by finiteness
    have hB' : ∀ k, B' k ≠ ∞ := fun k => by finiteness
    exact ENNReal.mul_ne_top hd (ENNReal.add_ne_top.2 ⟨hA', ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hc hd) (ENNReal.sum_ne_top.2 fun k _ =>
        ENNReal.add_ne_top.2 ⟨hB' k, hB' k⟩)⟩)
  intro N l x y z hxy hzy
  have hβ : 0 < 𝒯.deg i - 𝒯.deg j := by linarith
  unfold gammaDiffNearLeftGoodBound
  refine (gammaDiffNearGoodShape_le (σ := dyadicBase N ^ ((m : ℝ) *
      (𝒯.deg i - 𝒯.deg j + ρ)) * dyadicBase l ^ ((m : ℝ) * ρ)) (A' := A') (B' := B')
      ?_ ?_).trans_eq (by ring)
  · have h := gammaDiffUnitScale_term_le (β := 𝒯.deg i - 𝒯.deg j) (ρ := ρ) (K := 1) (a := 0) (b := e0) (m := m) zero_le_one
      (parabolicSemigroup.scaleDist_nonneg y x) (parabolicSemigroup.scaleDist_nonneg z y)
      le_rfl (by simp only [e0, hij, ↓reduceIte]; linarith)
      (by simp only [e0, hij, ↓reduceIte]; linarith) (by simp only [e0, hij, ↓reduceIte]; linarith)
      hxy hzy
    simpa only [Real.rpow_zero, one_mul, mul_one, e0, A'] using h
  · intro k hk
    obtain ⟨hjk, hki, hgood⟩ := gammaDiffUnitScale_mem_good hk
    have hgL := hρgap i k hki
    have hgR := hρgap k j hjk
    have hsum : 𝒯.deg i - 𝒯.deg j + ρ ≤ eL k + eR k := by
      simp only [eL, eR]
      by_cases h1 : (i, k) ∈ D
      · have h2 : (k, j) ∉ D := fun h2 => hgood ⟨h1, h2⟩
        simp only [h1, h2, ↓reduceIte]
        linarith
      · simp only [h1, ↓reduceIte]
        split_ifs <;> linarith
    have hR : ρ ≤ eR k := by
      simp only [eR]
      split_ifs <;> linarith
    have h := gammaDiffUnitScale_term_le (β := 𝒯.deg i - 𝒯.deg j) (ρ := ρ) (K := Cbar) (a := eL k) (b := eR k) (m := m) hCbar
      (parabolicSemigroup.scaleDist_nonneg y x) (parabolicSemigroup.scaleDist_nonneg z y)
      (by simp only [eL]; split_ifs <;> linarith) (by simp only [eR]; split_ifs <;> linarith)
      hsum hR hxy hzy
    simpa only [mul_one, eL, eR, B'] using h

/-- **Finite uniform scale constant for the right source-free near good bound.** -/
theorem gammaDiffNearRightGoodBound_finite_scale
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι)) (κ Cbar ρ : ℝ) {m : ℕ} (i j : ι)
    (hm : 1 ≤ m) (hCbar : 0 ≤ Cbar) (hκ : 0 < κ) (hρκ : ρ < κ)
    (hρgap : ∀ a b : ι, 𝒯.deg b < 𝒯.deg a → ρ < 𝒯.deg a - 𝒯.deg b)
    (hj : 𝒯.deg j < 𝒯.deg i) (hij : (i, j) ∉ D) :
    ∃ L : ℝ≥0∞, L ≠ ∞ ∧ ∀ (N l : ℕ) (x y z : ParabolicSpace),
      parabolicSemigroup.scaleDist x y ≤ 24 / (2 : ℝ) ^ N →
      parabolicSemigroup.scaleDist y z ≤ 4 / (2 : ℝ) ^ (N + l) →
      gammaDiffNearRightGoodBound 𝒯 D κ 1 Cbar 1 m i j x y z ≤
        L * dyadicBase N ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + ρ)) *
          dyadicBase l ^ ((m : ℝ) * ρ) := by
  classical
  let s := gammaGoodIntermediate 𝒯 D i j
  let eL : ι → ℝ := fun k => 𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)
  let eR : ι → ℝ := fun k => 𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)
  let e0 : ℝ := 𝒯.deg i - 𝒯.deg j + (if (i, j) ∈ D then 0 else κ)
  let A' : ℝ≥0∞ := ENNReal.ofReal (1 * (24 : ℝ) ^ (0 : ℝ) * 4 ^ e0) ^ m
  let B' : ι → ℝ≥0∞ := fun k => ENNReal.ofReal (Cbar * (24 : ℝ) ^ eR k * 4 ^ eL k) ^ m
  let c : ℝ≥0∞ := (s.card : ℝ≥0∞) ^ ((m : ℝ) - 1)
  let d : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((m : ℝ) - 1)
  have hc : c ≠ ∞ := gammaDiffUnitScale_card_ne_top s hm
  refine ⟨d * (A' + c * d * ∑ k ∈ s, (B' k + B' k)), ?_, ?_⟩
  · have hd : d ≠ ∞ := by finiteness
    have hA' : A' ≠ ∞ := by finiteness
    have hB' : ∀ k, B' k ≠ ∞ := fun k => by finiteness
    exact ENNReal.mul_ne_top hd (ENNReal.add_ne_top.2 ⟨hA', ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hc hd) (ENNReal.sum_ne_top.2 fun k _ =>
        ENNReal.add_ne_top.2 ⟨hB' k, hB' k⟩)⟩)
  intro N l x y z hxy hyz
  have hβ : 0 < 𝒯.deg i - 𝒯.deg j := by linarith
  unfold gammaDiffNearRightGoodBound
  refine (gammaDiffNearGoodShape_le (σ := dyadicBase N ^ ((m : ℝ) *
      (𝒯.deg i - 𝒯.deg j + ρ)) * dyadicBase l ^ ((m : ℝ) * ρ)) (A' := A') (B' := B')
      ?_ ?_).trans_eq (by ring)
  · have h := gammaDiffUnitScale_term_le (β := 𝒯.deg i - 𝒯.deg j) (ρ := ρ) (K := 1) (a := 0) (b := e0) (m := m) zero_le_one
      (parabolicSemigroup.scaleDist_nonneg x y) (parabolicSemigroup.scaleDist_nonneg y z)
      le_rfl (by simp only [e0, hij, ↓reduceIte]; linarith)
      (by simp only [e0, hij, ↓reduceIte]; linarith) (by simp only [e0, hij, ↓reduceIte]; linarith)
      hxy hyz
    simpa only [Real.rpow_zero, one_mul, mul_one, e0, A'] using h
  · intro k hk
    obtain ⟨hjk, hki, hgood⟩ := gammaDiffUnitScale_mem_good hk
    have hgL := hρgap i k hki
    have hgR := hρgap k j hjk
    have hsum : 𝒯.deg i - 𝒯.deg j + ρ ≤ eR k + eL k := by
      simp only [eL, eR]
      by_cases h1 : (i, k) ∈ D
      · have h2 : (k, j) ∉ D := fun h2 => hgood ⟨h1, h2⟩
        simp only [h1, h2, ↓reduceIte]
        linarith
      · simp only [h1, ↓reduceIte]
        split_ifs <;> linarith
    have hL : ρ ≤ eL k := by
      simp only [eL]
      split_ifs <;> linarith
    have h := gammaDiffUnitScale_term_le (β := 𝒯.deg i - 𝒯.deg j) (ρ := ρ) (K := Cbar) (a := eR k) (b := eL k) (m := m) hCbar
      (parabolicSemigroup.scaleDist_nonneg x y) (parabolicSemigroup.scaleDist_nonneg y z)
      (by simp only [eR]; split_ifs <;> linarith) (by simp only [eL]; split_ifs <;> linarith)
      hsum hL hxy hyz
    rw [mul_comm (parabolicSemigroup.scaleDist x y ^ eR k)] at h
    simpa only [mul_one, eL, eR, B'] using h

end RegularityStructures

end
