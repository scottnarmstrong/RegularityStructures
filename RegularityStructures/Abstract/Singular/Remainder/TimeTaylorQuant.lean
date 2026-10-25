/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.TaylorQuant
public import RegularityStructures.Abstract.Singular.Kernel.TimeTaylorBound

/-!
# Decay of the derivatives of the time-Taylor remainder

Quantitative form of `exists_norm_iteratedFDeriv_timeTaylorRem_le` (constants only depend on the
sup of the derivatives of `G` up to a fixed order) and its localisation to a decaying `G`
(`exists_remDecay_timeTaylorRem`): `‖D^i (timeTaylorRem τ m G) (w)‖ ≤ c B |τ|^m (1 + |w'|²)^{-3}`.
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem norm_iteratedFDeriv_remOp_le_of_sup {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (m : ℕ) {S : ℝ} (hS0 : 0 ≤ S) (hS : ∀ i ≤ m + 1 + 4, ∀ u, ‖iteratedFDeriv ℝ i g u‖ ≤ S)
    (τ : ℝ) {i : ℕ} (hi : i ≤ 4) (u : ParabolicSpace) :
    ‖iteratedFDeriv ℝ i (remOp timeDir τ m g) u‖ ≤ S * |τ| ^ (m + 1) := by
  have hQ : ContDiff ℝ ∞ (remOp timeDir τ m g) := contDiff_remOp hg timeDir τ m
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun d => ?_
  rw [Real.norm_eq_abs, iteratedFDeriv_apply_eq_lineIter_ofFn hQ, lineIter_remOp hg]
  refine (abs_remOp_le (contDiff_lineIter hg _) timeDir τ m u).trans ?_
  have hint : ∫ t in (0 : ℝ)..1, |(dirDeriv timeDir)^[m + 1] (lineIter (List.ofFn d) g)
      (u + (t * τ) • timeDir)| ≤ S * ∏ j, ‖d j‖ := by
    have hb : ∀ t : ℝ, |(dirDeriv timeDir)^[m + 1] (lineIter (List.ofFn d) g)
        (u + (t * τ) • timeDir)| ≤ S * ∏ j, ‖d j‖ := by
      intro t
      rw [← lineIter_replicate, ← lineIter_append]
      refine (abs_lineIter_le hg _ _).trans ?_
      rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
        norm_timeDir, one_pow, one_mul, List.map_ofFn, List.prod_ofFn]
      refine mul_le_mul_of_nonneg_right (hS _ (by simp; omega) _)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t => |(dirDeriv timeDir)^[m + 1] (lineIter (List.ofFn d) g)
        (u + (t * τ) • timeDir)|) (C := S * ∏ j, ‖d j‖) (fun t _ => by
          rw [Real.norm_eq_abs, abs_abs]; exact hb t)
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg zero_le_one
      fun t _ => abs_nonneg _), sub_zero, abs_one, mul_one] at this
    exact this
  calc _ ≤ |τ| ^ (m + 1) * (S * ∏ j, ‖d j‖) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = S * |τ| ^ (m + 1) * ∏ j, ‖d j‖ := by ring

theorem norm_iteratedFDeriv_timeTaylorRem_le_of_sup {g : ParabolicSpace → ℝ}
    (hg : ContDiff ℝ ∞ g) (m : ℕ) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ i ≤ m + 5, ∀ u, ‖iteratedFDeriv ℝ i g u‖ ≤ S) (τ : ℝ) {i : ℕ} (hi : i ≤ 4)
    (u : ParabolicSpace) : ‖iteratedFDeriv ℝ i (timeTaylorRem τ m g) u‖ ≤ S * |τ| ^ m := by
  cases m with
  | zero =>
    have : timeTaylorRem τ 0 g = fun w => g (w + τ • timeDir) := by
      funext w; simp [timeTaylorRem]
    rw [this, iteratedFDeriv_comp_add_right]
    simpa using hS i (by omega) _
  | succ m =>
    rw [timeTaylorRem_succ]
    exact norm_iteratedFDeriv_remOp_le_of_sup hg m hS0 (fun i hi => hS i (by omega)) τ hi u

/-- Decay of the derivatives of the time-Taylor remainder of a decaying function. -/
theorem exists_remDecay_timeTaylorRem (m : ℕ) :
    ∃ (n : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ {G : ParabolicSpace → ℝ} {B τ₀ : ℝ}, ContDiff ℝ ∞ G → 0 ≤ B →
      RemDecay G n τ₀ B → ∀ τ : ℝ, |τ| ≤ 1 → ∀ i ≤ 4, ∀ w : ParabolicSpace, w.1 + 4 ≤ τ₀ →
        ‖iteratedFDeriv ℝ i (timeTaylorRem τ m G) w‖ ≤ c * B * |τ| ^ m * remWt w.2 := by
  obtain ⟨c₁, hc₁, hloc⟩ := exists_localize (m + 5)
  refine ⟨m + 5, c₁, hc₁, fun {G B τ₀} hG hB hD τ hτ i hi w hw => ?_⟩
  obtain ⟨G', hG', hGc, heq, hbd⟩ := hloc hG hB hD w hw
  have hτn : ‖τ • timeDir‖ ≤ 1 := by rw [norm_smul, norm_timeDir]; simpa using hτ
  have hprof : timeTaylorRem τ m G =ᶠ[𝓝 w] timeTaylorRem τ m G' := by
    refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const :
        IsOpen {v : ParabolicSpace | ‖v - w‖ < 1}) (by simp)) fun v hv => ?_
    have hv' : ‖v - w‖ < 1 := hv
    have h1 : ‖v + τ • timeDir - w‖ < 3 := by
      have := norm_add_le (v - w) (τ • timeDir)
      rw [show v + τ • timeDir - w = (v - w) + τ • timeDir by abel]
      linarith
    have h0 : ‖v - w‖ < 3 := by linarith
    have hU : IsOpen {y : ParabolicSpace | ‖y - w‖ < 3} :=
      isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
    unfold timeTaylorRem
    rw [heq _ h1]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← lineIter_replicate, ← lineIter_replicate,
      lineIter_congr_of_isOpen hU (fun y hy => heq y hy) _ v h0]
  rw [(hprof.iteratedFDeriv ℝ i).self_of_nhds]
  have hS0 : 0 ≤ c₁ * B * remWt w.2 := by have := remWt_nonneg w.2; positivity
  have := norm_iteratedFDeriv_timeTaylorRem_le_of_sup hG' m hS0
    (fun N hN u => hbd N hN u) τ hi w
  refine this.trans (le_of_eq ?_)
  ring

end RegularityStructures

end
