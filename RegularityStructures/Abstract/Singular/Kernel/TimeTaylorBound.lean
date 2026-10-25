/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorBox
public import RegularityStructures.Analysis.Parabolic.Generator

/-!
# Derivative bounds for the time-Taylor remainder

For `g` smooth with compact support and `m : ℕ` there is `B` with
`‖D^i (remOp timeDir τ m g) u‖ ≤ B |τ|^{m+1}` for all `i ≤ 4`, `τ`, `u`
(`exists_norm_iteratedFDeriv_remOp_le`).  Here `remOp e τ m g = g(· + τ e) - T^m_τ g`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The time-Taylor remainder `g(w + τ e₀) - ∑_{j<m} τ^j/j! ∂_t^j g(w)`. -/
def timeTaylorRem (τ : ℝ) (m : ℕ) (g : ParabolicSpace → ℝ) (w : ParabolicSpace) : ℝ :=
  g (w + τ • timeDir) - ∑ j ∈ Finset.range m, (τ ^ j / (Nat.factorial j : ℝ)) *
    (dirDeriv timeDir)^[j] g w

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem timeTaylorRem_succ (τ : ℝ) (m : ℕ) (g : ParabolicSpace → ℝ) :
    timeTaylorRem τ (m + 1) g = remOp timeDir τ m g := by
  funext w
  simp only [timeTaylorRem, remOp, tayOp]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [div_eq_inv_mul, mul_assoc]

theorem iteratedFDeriv_apply_eq_lineIter_ofFn {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    {i : ℕ} (d : Fin i → ParabolicSpace) (w : ParabolicSpace) :
    iteratedFDeriv ℝ i f w d = lineIter (List.ofFn d) f w := by
  have h := congrFun (iteratedFDeriv_get_eq_lineIter hf (List.ofFn d)) w
  rw [← h]
  have key : ∀ (a : ℕ) (ha : a = i) (e : Fin a → ParabolicSpace),
      (∀ j, e j = d (Fin.cast ha j)) → iteratedFDeriv ℝ a f w e = iteratedFDeriv ℝ i f w d := by
    intro a ha
    subst ha
    intro e he
    have : e = d := funext fun j => by simpa using he j
    subst this
    rfl
  symm
  exact key _ (List.length_ofFn) _ fun j => by rw [List.get_ofFn]

theorem abs_lineIter_le {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g) (L : List ParabolicSpace)
    (w : ParabolicSpace) :
    |lineIter L g w| ≤ ‖iteratedFDeriv ℝ L.length g w‖ * (L.map fun d => ‖d‖).prod := by
  have h := congrFun (iteratedFDeriv_get_eq_lineIter hg L) w
  rw [← h]
  have := (iteratedFDeriv ℝ L.length g w).le_opNorm (fun j => L.get j)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  conv_rhs => rw [← List.ofFn_get (l := L), List.map_ofFn, List.prod_ofFn]
  rfl

theorem exists_norm_iteratedFDeriv_remOp_le {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℝ) (i : ℕ), i ≤ 4 → ∀ u : ParabolicSpace,
      ‖iteratedFDeriv ℝ i (remOp timeDir τ m g) u‖ ≤ B * |τ| ^ (m + 1) := by
  obtain ⟨B, hB0, hB⟩ := hc.exists_bound_iteratedFDeriv hg (m + 1 + 4)
  refine ⟨B, hB0, fun τ i hi u => ?_⟩
  have hQ : ContDiff ℝ ∞ (remOp timeDir τ m g) := contDiff_remOp hg timeDir τ m
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun d => ?_
  rw [Real.norm_eq_abs, iteratedFDeriv_apply_eq_lineIter_ofFn hQ, lineIter_remOp hg]
  refine (abs_remOp_le (contDiff_lineIter hg _) timeDir τ m u).trans ?_
  have hint : ∫ t in (0 : ℝ)..1, |(dirDeriv timeDir)^[m + 1] (lineIter (List.ofFn d) g)
      (u + (t * τ) • timeDir)| ≤ B * ∏ j, ‖d j‖ := by
    have hb : ∀ t : ℝ, |(dirDeriv timeDir)^[m + 1] (lineIter (List.ofFn d) g)
        (u + (t * τ) • timeDir)| ≤ B * ∏ j, ‖d j‖ := by
      intro t
      rw [← lineIter_replicate, ← lineIter_append]
      refine (abs_lineIter_le hg _ _).trans ?_
      rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
        norm_timeDir, one_pow, one_mul, List.map_ofFn, List.prod_ofFn]
      refine mul_le_mul_of_nonneg_right (hB _ (by simp; omega) _)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t => |(dirDeriv timeDir)^[m + 1] (lineIter (List.ofFn d) g)
        (u + (t * τ) • timeDir)|) (C := B * ∏ j, ‖d j‖) (fun t _ => by
          rw [Real.norm_eq_abs, abs_abs]; exact hb t)
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg zero_le_one
      fun t _ => abs_nonneg _), sub_zero, abs_one, mul_one] at this
    exact this
  calc _ ≤ |τ| ^ (m + 1) * (B * ∏ j, ‖d j‖) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = B * |τ| ^ (m + 1) * ∏ j, ‖d j‖ := by ring

theorem exists_norm_iteratedFDeriv_timeTaylorRem_le {g : ParabolicSpace → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℝ) (i : ℕ), i ≤ 4 → ∀ u : ParabolicSpace,
      ‖iteratedFDeriv ℝ i (timeTaylorRem τ m g) u‖ ≤ B * |τ| ^ m := by
  cases m with
  | zero =>
    obtain ⟨B, hB0, hB⟩ := hc.exists_bound_iteratedFDeriv hg 4
    refine ⟨B, hB0, fun τ i hi u => ?_⟩
    have : timeTaylorRem τ 0 g = fun w => g (w + τ • timeDir) := by
      funext w; simp [timeTaylorRem]
    rw [this, iteratedFDeriv_comp_add_right]
    simpa using hB i hi _
  | succ m =>
    obtain ⟨B, hB0, hB⟩ := exists_norm_iteratedFDeriv_remOp_le hg hc m
    refine ⟨B, hB0, fun τ i hi u => ?_⟩
    rw [timeTaylorRem_succ]
    exact hB τ i hi u

end RegularityStructures

end
