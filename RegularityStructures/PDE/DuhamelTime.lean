/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatTime
public import RegularityStructures.PDE.Duhamel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The time derivative of the Duhamel integral

* `norm_heatOp_apply_sub_le`: for `g` with two continuous derivatives, `t ↦ P_t g(x)` is
  Lipschitz on `ℝ` with constant `‖Δg‖`;
* `hasDerivAt_duhamel_apply`: if every `H(s)`, `s ∈ [0, T]`, has two continuous derivatives and the
  Laplacians form a continuous path, then for `t ∈ (0, T)`
  `∂_t ∫₀ᵗ P_{t-s} H(s) ds = H(t) + ∫₀ᵗ P_{t-s} ΔH(s) ds`.

For the second statement write `∫₀ᵗ P_{t-s} H(s) ds = ∫₀ᵀ (P_{t-s} H(s) - H(s)) ds + ∫₀ᵗ H(s) ds`;
the first integrand vanishes for `s ≥ t` because `P_τ` is the identity for `τ ≤ 0`, and is
Lipschitz in `t` uniformly in `s`, so it can be differentiated under the integral sign.
-/

public section

open MeasureTheory Set Filter Topology Real
open scoped Interval

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous function that is constant on `(-∞, 0]` and has derivative bounded by `C` on
`(0, ∞)` is `C`-Lipschitz on `ℝ`. -/
theorem norm_sub_le_mul_abs_of_hasDerivAt_pos {φ φ' : ℝ → E} {C : ℝ} (hc : Continuous φ)
    (hneg : ∀ τ ≤ 0, φ τ = φ 0) (hd : ∀ τ > 0, HasDerivAt φ (φ' τ) τ)
    (hb : ∀ τ > 0, ‖φ' τ‖ ≤ C) (a b : ℝ) : ‖φ a - φ b‖ ≤ C * |a - b| := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 1 one_pos)
  have key : ∀ a b, 0 < b → b ≤ a → ‖φ a - φ b‖ ≤ C * (a - b) := by
    intro a b hb0 hba
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f' := φ') (fun τ hτ => ?_)
      (fun τ hτ => hb τ (hb0.trans_le hτ.1)) a ⟨hba, le_rfl⟩
    exact (hd τ (hb0.trans_le hτ.1)).hasDerivWithinAt
  have key0 : ∀ a, 0 ≤ a → ‖φ a - φ 0‖ ≤ C * a := by
    intro a ha
    rcases ha.eq_or_lt with rfl | ha
    · simp
    have hlim : Tendsto (fun ε => ‖φ a - φ ε‖ - C * (a - ε)) (𝓝[>] 0)
        (𝓝 (‖φ a - φ 0‖ - C * (a - 0))) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact ((continuous_const.sub hc).norm.sub (continuous_const.mul
        (continuous_const.sub continuous_id))).tendsto 0
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖φ a - φ ε‖ - C * (a - ε) ≤ 0 := by
      filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
      linarith [key a ε hε.1 hε.2.le]
    have := le_of_tendsto hlim hev
    linarith
  -- the estimate for nonnegative times
  have hnn : ∀ a b, 0 ≤ a → 0 ≤ b → ‖φ a - φ b‖ ≤ C * |a - b| := by
    have half : ∀ a b, 0 ≤ a → 0 ≤ b → b ≤ a → ‖φ a - φ b‖ ≤ C * |a - b| := by
      intro a b ha hb hba
      rw [abs_of_nonneg (sub_nonneg.2 hba)]
      rcases hb.eq_or_lt with h | h
      · rw [← h, sub_zero]
        exact key0 a ha
      · exact key a b h hba
    intro a b ha hb
    rcases le_total b a with hba | hab
    · exact half a b ha hb hba
    · rw [norm_sub_rev, abs_sub_comm]
      exact half b a hb ha hab
  -- reduce to nonnegative times
  have hmax : ∀ τ, φ τ = φ (max τ 0) := by
    intro τ
    rcases le_total τ 0 with h | h
    · rw [max_eq_right h, hneg τ h]
    · rw [max_eq_left h]
  rw [hmax a, hmax b]
  exact (hnn _ _ (le_max_right _ _) (le_max_right _ _)).trans
    (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs a b 0) hC)

variable [CompleteSpace E]

/-- For `g` with two continuous derivatives, `t ↦ P_t g(x)` is `‖Δg‖`-Lipschitz on `ℝ`. -/
theorem norm_heatOp_apply_sub_le {g : C(Torus3, E)} {Dg : C(Torus3, Fin 3 → E)}
    {D2g : C(Torus3, Fin 3 → Fin 3 → E)} (hg : HasTorusDeriv g Dg)
    (hDg : HasTorusDeriv (E := Fin 3 → E) Dg D2g) (a b : ℝ) (x : Torus3) :
    ‖heatOp a g x - heatOp b g x‖ ≤ ‖torusLap D2g‖ * |a - b| := by
  refine norm_sub_le_mul_abs_of_hasDerivAt_pos (φ' := fun τ => heatOp τ (torusLap D2g) x)
    ((continuous_eval_const x).comp (continuous_heatOp_left g)) (fun τ hτ => ?_)
    (fun τ hτ => hasDerivAt_heatOp_apply hg hDg hτ x) (fun τ _ => norm_heatOp_apply_le _ _ _) a b
  show heatOp τ g x = heatOp 0 g x
  rw [heatOp_of_nonpos hτ, heatOp_zero_left]

omit [CompleteSpace E] in
/-- The Laplacian is postcomposition with the trace map `Fin 3 → Fin 3 → E → E`. -/
theorem torusLap_eq_compLeft (D2g : C(Torus3, Fin 3 → Fin 3 → E)) :
    torusLap D2g = (∑ i : Fin 3, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => E) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → E) i)).compLeftContinuous
        ℝ Torus3 D2g := by
  ext x
  simp [torusLap_apply]

omit [CompleteSpace E] in
theorem continuous_torusLap_comp {D : ℝ → C(Torus3, Fin 3 → Fin 3 → E)} (hD : Continuous D) :
    Continuous fun s => torusLap (D s) := by
  simp_rw [torusLap_eq_compLeft]
  exact (ContinuousLinearMap.continuous _).comp hD

/-- **Time derivative of the Duhamel integral.** -/
theorem hasDerivAt_duhamel_apply {H : ℝ → C(Torus3, E)} {DH : ℝ → C(Torus3, Fin 3 → E)}
    {D2H : ℝ → C(Torus3, Fin 3 → Fin 3 → E)} (hH : Continuous H) (hD2H : Continuous D2H)
    {T : ℝ} (hd1 : ∀ s ∈ Icc 0 T, HasTorusDeriv (H s) (DH s))
    (hd2 : ∀ s ∈ Icc 0 T, HasTorusDeriv (E := Fin 3 → E) (DH s) (D2H s)) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo 0 T) (x : Torus3) :
    HasDerivAt (fun t => duhamel H t x)
      (H t₀ x + duhamel (fun s => torusLap (D2H s)) t₀ x) t₀ := by
  set ΔH : ℝ → C(Torus3, E) := fun s => torusLap (D2H s) with hΔHdef
  have hΔH : Continuous ΔH := continuous_torusLap_comp hD2H
  obtain ⟨M, hM⟩ : ∃ M, ∀ s ∈ Icc 0 T, ‖ΔH s‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn hΔH.continuousOn
  have hT : 0 ≤ T := (ht₀.1.trans ht₀.2).le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hHx : Continuous fun s => H s x := (continuous_eval_const x).comp hH
  set K : ℝ → ℝ → E := fun t s => heatOp (t - s) (H s) x - H s x with hKdef
  have hKc : ∀ t, Continuous (K t) := fun t =>
    ((continuous_eval_const x).comp ((continuous_const.sub continuous_id).heatOp hH)).sub hHx
  have hK0 : ∀ t s, t ≤ s → K t s = 0 := by
    intro t s h
    simp [hKdef, heatOp_of_nonpos (sub_nonpos.2 h)]
  -- the decomposition, valid for `t ∈ [0, T]`
  have hdecomp : ∀ t ∈ Icc 0 T, duhamel H t x = (∫ s in (0 : ℝ)..T, K t s) +
      ∫ s in (0 : ℝ)..t, H s x := by
    intro t ht
    rw [duhamel_apply hH]
    have hsplit : ∫ s in (0 : ℝ)..T, K t s = ∫ s in (0 : ℝ)..t, K t s := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := t)
        ((hKc t).intervalIntegrable 0 t) ((hKc t).intervalIntegrable t T)]
      have hz : ∫ s in t..T, K t s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : E)) fun s hs => ?_]
        · simp
        · rw [uIcc_of_le ht.2] at hs
          exact hK0 t s hs.1
      rw [hz, add_zero]
    have hsub := intervalIntegral.integral_sub (μ := volume) (a := 0) (b := t)
      (f := fun s => heatOp (t - s) (H s) x) (g := fun s => H s x)
      (((continuous_eval_const x).comp
        ((continuous_const.sub continuous_id).heatOp hH)).intervalIntegrable 0 t)
      (hHx.intervalIntegrable 0 t)
    rw [hsplit, hKdef]
    simp only
    rw [hsub, sub_add_cancel]
  -- the derivative of the first part
  set F' : ℝ → E := (Iio t₀).indicator fun s => heatOp (t₀ - s) (ΔH s) x with hF'def
  have hF'c : Continuous fun s => heatOp (t₀ - s) (ΔH s) x :=
    (continuous_eval_const x).comp ((continuous_const.sub continuous_id).heatOp hΔH)
  have hlip : ∀ᵐ s ∂volume, s ∈ Ι 0 T →
      LipschitzOnWith (Real.nnabs M) (fun t => K t s) univ := by
    refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le hT] at hs
    have hsI : s ∈ Icc 0 T := Ioc_subset_Icc_self hs
    refine LipschitzOnWith.of_dist_le_mul fun t _ t' _ => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_nnabs, abs_of_nonneg hM0, hKdef]
    simp only [sub_sub_sub_cancel_right]
    refine (norm_heatOp_apply_sub_le (hd1 s hsI) (hd2 s hsI) _ _ x).trans ?_
    rw [sub_sub_sub_cancel_right, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM s hsI) (norm_nonneg _)
  have hdiff : ∀ᵐ s ∂volume, s ∈ Ι 0 T → HasDerivAt (fun t => K t s) (F' s) t₀ := by
    filter_upwards [Measure.ae_ne volume t₀] with s hst hs
    rw [uIoc_of_le hT] at hs
    have hsI : s ∈ Icc 0 T := Ioc_subset_Icc_self hs
    rcases lt_or_gt_of_ne hst with h | h
    · rw [hF'def, indicator_of_mem (mem_Iio.2 h)]
      have h1 := hasDerivAt_heatOp_apply (hd1 s hsI) (hd2 s hsI) (sub_pos.2 h) x
      have h2 := h1.scomp t₀ ((hasDerivAt_id' t₀).sub_const s)
      simpa [hKdef] using h2.sub_const (H s x)
    · rw [hF'def, indicator_of_notMem (by simpa using h.le)]
      refine (hasDerivAt_const t₀ (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with t ht
      exact hK0 t s (le_of_lt ht)
  obtain ⟨hF'int, hD1⟩ := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume)
    (F := K) (F' := F') (bound := fun _ => M) (s := univ) univ_mem
    (Eventually.of_forall fun t => (hKc t).aestronglyMeasurable)
    ((hKc t₀).intervalIntegrable 0 T)
    (hF'c.aestronglyMeasurable.indicator measurableSet_Iio) hlip intervalIntegrable_const
    hdiff)
  -- the derivative of the second part
  have hD2 : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, H s x) (H t₀ x) t₀ :=
    intervalIntegral.integral_hasDerivAt_right (hHx.intervalIntegrable 0 t₀)
      (hHx.stronglyMeasurableAtFilter _ _) hHx.continuousAt
  -- the value of the first derivative
  have hval : ∫ s in (0 : ℝ)..T, F' s = duhamel ΔH t₀ x := by
    have hsub1 : uIcc 0 t₀ ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht₀.1.le, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht₀.2.le
    have hsub2 : uIcc t₀ T ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht₀.2.le, uIcc_of_le hT]
      exact Icc_subset_Icc ht₀.1.le le_rfl
    rw [duhamel_apply hΔH, ← intervalIntegral.integral_add_adjacent_intervals (b := t₀)
      (hF'int.mono_set hsub1) (hF'int.mono_set hsub2)]
    have hz : ∫ s in t₀..T, F' s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : E)) fun s hs => ?_]
      · simp
      · rw [uIcc_of_le ht₀.2.le] at hs
        exact indicator_of_notMem (by simpa using hs.1) _
    rw [hz, add_zero]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume t₀] with s hne hs
    rw [uIoc_of_le ht₀.1.le] at hs
    exact indicator_of_mem (mem_Iio.2 (lt_of_le_of_ne hs.2 hne)) _
  have hsum := hD1.add hD2
  rw [hval] at hsum
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv (add_comm _ _)
  filter_upwards [Icc_mem_nhds ht₀.1 ht₀.2] with t ht
  exact hdecomp t ht

end RegularityStructures.PDE

end
