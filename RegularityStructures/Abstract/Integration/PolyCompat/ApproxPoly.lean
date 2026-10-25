/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyCompat.Approx

/-!
# Approximate identity for `parabolicSemigroup` on continuous functions of polynomial growth

`Q_s g (z) → g (z)` as `s ↓ 0` for continuous `g` with `|g u| ≤ B (1 + ‖u‖_𝔰)^n`
(`tendsto_apply_parabolicSemigroup_nhdsGT`), by the near/far splitting of
`RegularisingSemigroup.tendsto_apply_nhdsGT_of_growth`.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures

variable {g : ParabolicSpace → ℝ}

/-- Near/far growth estimate for the oscillation of a continuous function of polynomial growth. -/
theorem exists_oscillation_growth (hc : Continuous g) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n) (z : ParabolicSpace) :
    ∀ ε > 0, ∃ A : ℝ, 0 ≤ A ∧ ∀ y, |g y - g z| ≤
      ε + A * parabolicNorm (y - z) + A * parabolicNorm (y - z) ^ (n + 1) := by
  intro ε hε
  obtain ⟨δ, hδ, hcδ⟩ := parabolicSemigroup_continuity hc z ε hε
  have hB0 : 0 ≤ B := nonneg_of_bound hB
  have hz0 := parabolicNorm_nonneg z
  set C : ℝ := B * (1 + parabolicNorm z) ^ n + |g z| with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C * 2 ^ n / δ, by positivity, fun y => ?_⟩
  set d := parabolicNorm (y - z) with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hA0 : 0 ≤ C * 2 ^ n / δ := by positivity
  by_cases hy : d < δ
  · have := hcδ y hy
    have h1 : 0 ≤ C * 2 ^ n / δ * d := by positivity
    have h2 : 0 ≤ C * 2 ^ n / δ * d ^ (n + 1) := by positivity
    linarith
  · replace hy := not_lt.1 hy
    have h1 : 1 + parabolicNorm y ≤ (1 + parabolicNorm z) * (1 + d) := by
      have := one_add_parabolicNorm_le y z
      linarith
    have h2 : (1 + parabolicNorm y) ^ n ≤ (1 + parabolicNorm z) ^ n * (1 + d) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg y]) h1 n
    have h3 : 1 ≤ (1 + d) ^ n := one_le_pow₀ (by linarith)
    have h4 : |g y - g z| ≤ C * (1 + d) ^ n := by
      calc |g y - g z| ≤ |g y| + |g z| := abs_sub _ _
        _ ≤ B * ((1 + parabolicNorm z) ^ n * (1 + d) ^ n) + |g z| := by
          have := mul_le_mul_of_nonneg_left h2 hB0
          linarith [hB y]
        _ ≤ C * (1 + d) ^ n := by
          rw [hC]
          have := mul_le_mul_of_nonneg_left h3 (abs_nonneg (g z))
          nlinarith
    have h5 : (1 + d) ^ n ≤ 2 ^ n * (1 + d ^ n) := one_add_pow_le d hd0 n
    have h6 : C * 2 ^ n * (1 + d ^ n) ≤ C * 2 ^ n / δ * d * (1 + d ^ n) := by
      have : C * 2 ^ n ≤ C * 2 ^ n / δ * d := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        exact mul_le_mul_of_nonneg_left hy (by positivity)
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h7 : C * (1 + d) ^ n ≤ C * 2 ^ n * (1 + d ^ n) := by
      calc C * (1 + d) ^ n ≤ C * (2 ^ n * (1 + d ^ n)) := mul_le_mul_of_nonneg_left h5 hC0
        _ = _ := by ring
    have h8 : C * 2 ^ n / δ * d * (1 + d ^ n) =
        C * 2 ^ n / δ * d + C * 2 ^ n / δ * d ^ (n + 1) := by ring
    linarith

/-- Approximate identity for continuous functions of polynomial growth:
`Q_s g (z) → g (z)` as `s ↓ 0`. -/
theorem tendsto_apply_parabolicSemigroup_nhdsGT (hc : Continuous g) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n) (z : ParabolicSpace) :
    Tendsto (fun s => parabolicSemigroup.apply s g z) (𝓝[>] 0) (𝓝 (g z)) :=
  parabolicSemigroup.tendsto_apply_nhdsGT_of_growth parabolicSemigroup_isConservative z n
    (fun _ hs => integrable_parabolicKernel_mul_of_bound hc.measurable hB hs z)
    (exists_oscillation_growth hc hB z)

/-- Target 1 in `PolyBounded` form: `Q_s g (z) → g (z)` as `s ↓ 0` for continuous `g` of
polynomial growth. -/
theorem PolyBounded.tendsto_apply_nhdsGT (hg : PolyBounded g) (hc : Continuous g)
    (z : ParabolicSpace) :
    Tendsto (fun s => parabolicSemigroup.apply s g z) (𝓝[>] 0) (𝓝 (g z)) := by
  obtain ⟨_, _, _, hB⟩ := hg
  exact tendsto_apply_parabolicSemigroup_nhdsGT hc hB z

end RegularityStructures

end
