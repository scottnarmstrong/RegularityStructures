/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Decay
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Localisation of a decaying function by a cutoff

If `G` has `RemDecay G n τ₀ B` and `u₀.1 + 4 ≤ τ₀`, then `G' = κ(· − u₀) G` agrees with `G`
on the ball `‖w − u₀‖ < 3` (product norm) and has *global* derivative bounds
`‖D^N G'‖ ≤ c B (1 + |u₀'|²)^{-3}` for `N ≤ n` (`exists_localize`).  Applied to the quantitative
Taylor lemmas, this turns global supremum bounds into decay bounds at the point `u₀`.
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

/-- Peetre-type comparison of the weights at two spatial points at distance `≤ ρ` in every
coordinate. -/
theorem remWt_le_mul_remWt {a b : Fin 3 → ℝ} {ρ : ℝ} (h : ∀ i, |a i - b i| ≤ ρ) :
    remWt b ≤ (2 + 6 * ρ ^ 2) ^ 3 * remWt a := by
  have hSa := sqNorm3_nonneg a
  have hSb := sqNorm3_nonneg b
  have hsq : sqNorm3 a ≤ 2 * sqNorm3 b + 6 * ρ ^ 2 := by
    unfold sqNorm3
    have h1 : ∀ i, a i ^ 2 ≤ 2 * b i ^ 2 + 2 * ρ ^ 2 := fun i => by
      have h2 : (a i - b i) ^ 2 ≤ ρ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      nlinarith [sq_nonneg (2 * b i - a i), h2]
    calc ∑ i, a i ^ 2 ≤ ∑ i, (2 * b i ^ 2 + 2 * ρ ^ 2) := Finset.sum_le_sum fun i _ => h1 i
      _ = 2 * ∑ i, b i ^ 2 + 6 * ρ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin]
        simp only [nsmul_eq_mul]; push_cast; ring
  have hA : 0 < 1 + sqNorm3 a := by linarith
  have hB : 0 < 1 + sqNorm3 b := by linarith
  have hc : 1 + sqNorm3 a ≤ (2 + 6 * ρ ^ 2) * (1 + sqNorm3 b) := by
    nlinarith [sq_nonneg ρ, mul_nonneg (sq_nonneg ρ) hSb]
  have h1 : (1 + sqNorm3 b)⁻¹ ≤ (2 + 6 * ρ ^ 2) * (1 + sqNorm3 a)⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hB hA]
    linarith
  unfold remWt
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h1 3

theorem abs_snd_sub_le_norm (w v : ParabolicSpace) (i : Fin 3) : |w.2 i - v.2 i| ≤ ‖w - v‖ := by
  rw [← Real.norm_eq_abs]
  have := norm_le_pi_norm (w - v).2 i
  exact (by simpa using this : ‖w.2 i - v.2 i‖ ≤ ‖(w - v).2‖).trans (norm_snd_le _)

theorem abs_fst_sub_le_norm (w v : ParabolicSpace) : |w.1 - v.1| ≤ ‖w - v‖ := by
  rw [← Real.norm_eq_abs]
  exact (by simpa using norm_fst_le (w - v) : ‖w.1 - v.1‖ ≤ ‖w - v‖)

/-- Localisation by a cutoff: global derivative bounds for a function agreeing with `G` near `u₀`. -/
theorem exists_localize (n : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {G : ParabolicSpace → ℝ} {B τ₀ : ℝ}, ContDiff ℝ ∞ G → 0 ≤ B →
      RemDecay G n τ₀ B → ∀ u₀ : ParabolicSpace, u₀.1 + 4 ≤ τ₀ →
      ∃ G' : ParabolicSpace → ℝ, ContDiff ℝ ∞ G' ∧ HasCompactSupport G' ∧
        (∀ w, ‖w - u₀‖ < 3 → G' w = G w) ∧
        ∀ N ≤ n, ∀ w, ‖iteratedFDeriv ℝ N G' w‖ ≤ c * B * remWt u₀.2 := by
  let b : ContDiffBump (0 : ParabolicSpace) := ⟨3, 4, by norm_num, by norm_num⟩
  obtain ⟨Ck, hCk0, hCk⟩ := b.hasCompactSupport.exists_bound_iteratedFDeriv b.contDiff n
  refine ⟨2 ^ n * Ck * (2 + 6 * (4 : ℝ) ^ 2) ^ 3, by positivity, fun {G B τ₀} hG hB hD u₀ hu₀ =>
    ⟨fun w => b (w - u₀) * G w, ?_, ?_, ?_, ?_⟩⟩
  · exact (b.contDiff.comp (contDiff_id.sub contDiff_const)).mul hG
  · refine HasCompactSupport.intro (isCompact_closedBall u₀ 4) fun w hw => ?_
    have : b (w - u₀) = 0 := b.zero_of_le_dist (by
      rw [dist_zero_right]
      have : 4 < dist w u₀ := by simpa using hw
      rw [dist_eq_norm] at this; exact this.le)
    simp [this]
  · intro w hw
    have : b (w - u₀) = 1 := b.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff]; exact (show ‖w - u₀‖ ≤ 3 from hw.le))
    simp [this]
  · intro N hN w
    have hbk : ContDiff ℝ ∞ (fun w => b (w - u₀)) := b.contDiff.comp (contDiff_id.sub contDiff_const)
    by_cases hw : ‖w - u₀‖ ≤ 4
    · have hτ : w.1 ≤ τ₀ := by
        have := abs_fst_sub_le_norm w u₀
        have := (abs_le.1 (this.trans hw)).2
        linarith
      have hwt : remWt w.2 ≤ (2 + 6 * (4 : ℝ) ^ 2) ^ 3 * remWt u₀.2 :=
        remWt_le_mul_remWt fun i => (abs_snd_sub_le_norm u₀ w i).trans
          (by rw [norm_sub_rev]; exact hw)
      refine (norm_iteratedFDeriv_mul_le hbk hG w (n := N) (by exact_mod_cast le_top)).trans ?_
      have hterm : ∀ i ∈ Finset.range (N + 1), (N.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun w => b (w - u₀)) w‖ * ‖iteratedFDeriv ℝ (N - i) G w‖ ≤
          (N.choose i : ℝ) * (Ck * (B * ((2 + 6 * (4 : ℝ) ^ 2) ^ 3 * remWt u₀.2))) := by
        intro i hi
        have hiN : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 : ‖iteratedFDeriv ℝ i (fun w => b (w - u₀)) w‖ ≤ Ck := by
          have e : (fun w => b (w - u₀)) = fun w => b (w + -u₀) := by
            funext w; rw [sub_eq_add_neg]
          rw [e, iteratedFDeriv_comp_add_right]
          exact hCk i (hiN.trans hN) _
        have h2 : ‖iteratedFDeriv ℝ (N - i) G w‖ ≤ B * ((2 + 6 * (4 : ℝ) ^ 2) ^ 3 * remWt u₀.2) :=
          (hD (N - i) ((Nat.sub_le _ _).trans hN) w hτ).trans
            (mul_le_mul_of_nonneg_left hwt hB)
        have h3 : 0 ≤ B * ((2 + 6 * (4 : ℝ) ^ 2) ^ 3 * remWt u₀.2) :=
          mul_nonneg hB (mul_nonneg (by positivity) (remWt_nonneg _))
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hCk0) (by positivity)
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hsum : ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) = 2 ^ N := by
        exact_mod_cast Nat.sum_range_choose N
      have h2n : (2 : ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hN
      have hX : 0 ≤ Ck * (B * ((2 + 6 * (4 : ℝ) ^ 2) ^ 3 * remWt u₀.2)) :=
        mul_nonneg hCk0 (mul_nonneg hB (mul_nonneg (by positivity) (remWt_nonneg _)))
      rw [hsum]
      calc (2 : ℝ) ^ N * (Ck * (B * ((2 + 6 * (4 : ℝ) ^ 2) ^ 3 * remWt u₀.2)))
          ≤ 2 ^ n * (Ck * (B * ((2 + 6 * (4 : ℝ) ^ 2) ^ 3 * remWt u₀.2))) :=
            mul_le_mul_of_nonneg_right h2n hX
        _ = _ := by ring
    · push Not at hw
      have hev : (fun w => b (w - u₀) * G w) =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
        refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds
          (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
          hw) fun v hv => ?_
        have : b (v - u₀) = 0 := b.zero_of_le_dist (by
          rw [dist_zero_right]; exact (show (4 : ℝ) < ‖v - u₀‖ from hv).le)
        simp [this]
      rw [(hev.iteratedFDeriv ℝ N).self_of_nhds]
      simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      have : 0 ≤ remWt u₀.2 := remWt_nonneg _
      positivity

end RegularityStructures

end
