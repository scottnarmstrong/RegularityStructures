/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.DiffPairing
public import RegularityStructures.Analysis.Heat.Schauder.Index

/-!
# Hölder continuity of the heat convolution

For `Λ ∈ parabolicSemigroup.distributions` of global order `α ∈ (-2, -1)` (so `0 < α + 2 < 1`),
`|(K * Λ)(x) - (K * Λ)(y)| ≤ c₂ C ‖x - y‖_𝔰^{α+2}` (`exists_abs_heatConv_sub_le`): this is the
Hölder case of the Schauder estimate, "`K *` maps `C^α` to `C^{α+2}`" [Hai14, Section 5].

The shell sum is split at `m` with `1/4 < ‖x - y‖_𝔰 2^m ≤ 1/2`: for `n < m` the increments of
the pairings are bounded by `c₃ C ‖x - y‖_𝔰 2^{-(α+1) n}` (`RegularityStructures.Analysis.Heat.Schauder.DiffPairing`), a geometric sum
dominated by its last term; for `n ≥ m` each pairing is bounded separately by `c₀ C 2^{-(α+2) n}`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem abs_head_sum_le {f : ℕ → ℝ} {K d ρ : ℝ} (hρ : 1 < ρ) (hK : 0 ≤ K) (hd : 0 ≤ d) (m : ℕ)
    (hf : ∀ n < m, |f n| ≤ K * d * ρ ^ n) :
    |∑ n ∈ Finset.range m, f n| ≤ K * d * ρ ^ m / (ρ - 1) := by
  have hρ1 : 0 < ρ - 1 := by linarith
  calc |∑ n ∈ Finset.range m, f n| ≤ ∑ n ∈ Finset.range m, |f n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range m, K * d * ρ ^ n :=
        Finset.sum_le_sum fun n hn => hf n (Finset.mem_range.1 hn)
    _ = K * d * ((ρ ^ m - 1) / (ρ - 1)) := by
        rw [← Finset.mul_sum, geom_sum_eq hρ.ne']
    _ ≤ K * d * (ρ ^ m / (ρ - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK hd)
        exact div_le_div_of_nonneg_right (by linarith) hρ1.le
    _ = _ := by ring

theorem abs_tail_tsum_le {f : ℕ → ℝ} {K r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ)
    (hf : ∀ n, |f (n + m)| ≤ K * r ^ (n + m)) :
    |∑' n, f (n + m)| ≤ K * r ^ m / (1 - r) := by
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (K * r ^ m)
  have h := tsum_of_norm_bounded hg fun n => by
    rw [Real.norm_eq_abs]
    refine (hf n).trans (le_of_eq ?_)
    rw [pow_add]; ring
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  have : 1 - r ≠ 0 := (sub_pos.2 hr1).ne'
  field_simp

/-- **Hölder estimate** (target 3): for `-2 < α < -1`,
`|(K * Λ)(x) - (K * Λ)(y)| ≤ c₂ C ‖x - y‖_𝔰^{α+2}`, with `c₂` depending only on `α`. -/
theorem exists_abs_heatConv_sub_le {α : ℝ} (hα1 : -2 < α) (hα2 : α < -1) :
    ∃ c₂ : ℝ, 0 ≤ c₂ ∧ ∀ {Λ : ℝ → ParabolicSpace → ℝ} {C : ℝ},
      Λ ∈ parabolicSemigroup.distributions → (∀ u, 0 < u → Measurable (Λ u)) → 0 ≤ C →
      (∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ C * u ^ (α / 4)) →
      ∀ x y : ParabolicSpace,
        |heatConv Λ x - heatConv Λ y| ≤ c₂ * C * parabolicNorm (x - y) ^ (α + 2) := by
  obtain ⟨c₃, hc₃, hinc⟩ := exists_abs_pairing_heatShell_sub_le hα1
  have hρ : 1 < (2 : ℝ) ^ (-(α + 1)) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hr0 := (shellRatio_pos α).le
  have hr1 := shellRatio_lt_one hα1
  have hc₀ := shellPairingConst_nonneg (α := α) (by linarith)
  have hc₁ := heatConvConst_nonneg hα1
  refine ⟨8 * heatConvConst α + c₃ / ((2 : ℝ) ^ (-(α + 1)) - 1) +
    8 * shellPairingConst α / (1 - shellRatio α), ?_, ?_⟩
  · exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) hc₁)
      (div_nonneg hc₃ (by linarith))) (div_nonneg (mul_nonneg (by norm_num) hc₀) (by linarith))
  intro Λ C hΛ hΛm hC hloc x y
  set d := parabolicNorm (x - y) with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hdγ : 0 ≤ d ^ (α + 2) := Real.rpow_nonneg hd0 _
  have hx := summable_pairing_heatShell hΛ hΛm hα1 hC hloc x
  have hy := summable_pairing_heatShell hΛ hΛm hα1 hC hloc y
  have hsub : heatConv Λ x - heatConv Λ y = ∑' n, (parabolicSemigroup.pairing Λ
      (fun z => heatShell n (x - z)) - parabolicSemigroup.pairing Λ (fun z => heatShell n (y - z))) :=
    (hx.tsum_sub hy).symm
  have hcC : 0 ≤ C * d ^ (α + 2) := mul_nonneg hC hdγ
  rcases lt_or_ge d (1 / 4) with hd1 | hd1
  · rcases hd0.eq_or_lt with hd00 | hdpos
    · -- `d = 0`: every increment vanishes
      rw [hsub]
      have : ∀ n : ℕ, parabolicSemigroup.pairing Λ (fun z => heatShell n (x - z)) -
          parabolicSemigroup.pairing Λ (fun z => heatShell n (y - z)) = 0 := by
        intro n
        have h := hinc hΛ hΛm hC hloc n x y (by rw [← hd, ← hd00]; simp)
        rw [← hd, ← hd00] at h
        simpa using h
      simp only [this, tsum_zero, abs_zero]
      refine mul_nonneg (mul_nonneg ?_ hC) hdγ
      exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) hc₁)
        (div_nonneg hc₃ (by linarith))) (div_nonneg (mul_nonneg (by norm_num) hc₀) (by linarith))
    · obtain ⟨m, hm, h1, h2⟩ := exists_splitIndex hα1 hα2 hdpos hd1
      rw [hsub, ← (hx.sub hy).sum_add_tsum_nat_add m]
      set f : ℕ → ℝ := fun n => parabolicSemigroup.pairing Λ (fun z => heatShell n (x - z)) -
        parabolicSemigroup.pairing Λ (fun z => heatShell n (y - z)) with hf
      have hhead := abs_head_sum_le (f := f) (K := c₃ * C) (d := d) hρ (mul_nonneg hc₃ hC) hd0 m
        fun n hn => by
          have h := hinc hΛ hΛm hC hloc n x y (by linarith [hm n hn])
          rw [Real.rpow_mul_natCast (by norm_num)] at h
          exact h
      have htail := abs_tail_tsum_le (f := f) (K := 2 * shellPairingConst α * C) hr0 hr1 m
        fun n => by
          have hx' := abs_pairing_heatShell_le hΛ hΛm hα1 hC hloc (n + m) x
          have hy' := abs_pairing_heatShell_le hΛ hΛm hα1 hC hloc (n + m) y
          rw [two_rpow_neg_mul_nat] at hx' hy'
          refine (abs_sub _ _).trans ?_
          linarith
      set ρ : ℝ := (2 : ℝ) ^ (-(α + 1)) with hρdef
      set A : ℝ := c₃ / (ρ - 1) with hA
      set B : ℝ := 8 * shellPairingConst α / (1 - shellRatio α) with hB
      have hρ1 : 0 < ρ - 1 := by linarith
      have h1r : 0 < 1 - shellRatio α := by linarith
      have hA0 : 0 ≤ A := div_nonneg hc₃ hρ1.le
      have hB0 : 0 ≤ B := div_nonneg (mul_nonneg (by norm_num) hc₀) h1r.le
      have t1 : c₃ * C * d * ρ ^ m / (ρ - 1) ≤ A * (C * d ^ (α + 2)) := by
        have : c₃ * C * d * ρ ^ m / (ρ - 1) = A * C * (d * ρ ^ m) := by rw [hA]; ring
        rw [this, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hC) hA0
      have t2 : 2 * shellPairingConst α * C * shellRatio α ^ m / (1 - shellRatio α) ≤
          B * (C * d ^ (α + 2)) := by
        have : 2 * shellPairingConst α * C * shellRatio α ^ m / (1 - shellRatio α) =
            (2 * shellPairingConst α / (1 - shellRatio α)) * C * shellRatio α ^ m := by ring
        rw [this]
        have hB' : B * (C * d ^ (α + 2)) =
            (2 * shellPairingConst α / (1 - shellRatio α)) * C * (4 * d ^ (α + 2)) := by
          rw [hB]; ring
        rw [hB', mul_assoc _ C, mul_assoc _ C]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC) ?_
        exact div_nonneg (mul_nonneg (by norm_num) hc₀) h1r.le
      have t3 : 0 ≤ heatConvConst α * (C * d ^ (α + 2)) := mul_nonneg hc₁ hcC
      calc |(∑ n ∈ Finset.range m, f n) + ∑' n, f (n + m)|
          ≤ |∑ n ∈ Finset.range m, f n| + |∑' n, f (n + m)| := abs_add_le _ _
        _ ≤ _ := add_le_add hhead htail
        _ ≤ A * (C * d ^ (α + 2)) + B * (C * d ^ (α + 2)) := add_le_add t1 t2
        _ ≤ _ := by linarith
  · -- `d ≥ 1/4`: use the sup bound
    have h1 := abs_heatConv_le hΛ hΛm hα1 hC hloc x
    have h2 := abs_heatConv_le hΛ hΛm hα1 hC hloc y
    have hdγ4 : 1 / 4 ≤ d ^ (α + 2) := by
      calc (1 / 4 : ℝ) = (1 / 4) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 4) ^ (α + 2) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
        _ ≤ d ^ (α + 2) := Real.rpow_le_rpow (by norm_num) hd1 (by linarith)
    have hA0 : 0 ≤ c₃ / ((2 : ℝ) ^ (-(α + 1)) - 1) := div_nonneg hc₃ (by linarith)
    have hB0 : 0 ≤ 8 * shellPairingConst α / (1 - shellRatio α) :=
      div_nonneg (mul_nonneg (by norm_num) hc₀) (by linarith)
    have hcc : 0 ≤ heatConvConst α * C := mul_nonneg hc₁ hC
    calc |heatConv Λ x - heatConv Λ y| ≤ |heatConv Λ x| + |heatConv Λ y| := abs_sub _ _
      _ ≤ 2 * (heatConvConst α * C) := by linarith
      _ ≤ 8 * heatConvConst α * C * d ^ (α + 2) := by
          have := mul_le_mul_of_nonneg_left hdγ4 hcc
          linarith
      _ ≤ _ := by linarith [mul_nonneg hA0 hcC, mul_nonneg hB0 hcC]

end RegularityStructures

end
