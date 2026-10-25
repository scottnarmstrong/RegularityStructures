/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePotentialIntegrability
public import Phi43.Stochastic.StochasticHeatConvergenceSemigroup
public import RegularityStructures.PDE.HeatOpBridge
public import RegularityStructures.PDE.MildSmooth
public import RegularityStructures.Abstract.Datum.HeatField
public import RegularityStructures.Torus.KernelBoundsLargeTime
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import RegularityStructures.Statements.Defs.IsMassivePotential

/-!
# Smoothness of massive potentials

This module prepares the local causal-semigroup argument for the smoothness part of the convergence
of the noise potentials (`phi43Noise_cauchy`).  A continuous initial profile contributes a
positive-time heat field, and a smooth forcing contributes a smooth zero-initial-data Duhamel term.
The remaining identity, expressing the massive potential as this sum on every finite time window, is
proved below from the periodised heat-kernel semigroup identity.

The kernel is the massive resolvent kernel of equation (2.2) of the statement; the local
regularity assertion is the analytic content of Hairer [Hai14], Proposition 8.27.
-/

public noncomputable section

open MeasureTheory Set Real
open RegularityStructures.PDE

namespace RegularityStructures.Phi43

private def forcingPath (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f) (t : ℝ) :
    C(Torus3, ℝ) :=
  ⟨fun x => f (t, x), (Continuous.continuous_of_isSmoothOnSpaceTime hf).comp
    (continuous_const.prodMk continuous_id)⟩

private theorem continuous_forcingPath {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) :
    Continuous (forcingPath f hf) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (Continuous.continuous_of_isSmoothOnSpaceTime hf).comp
    (continuous_fst.prodMk continuous_snd)

private def forcingNonlinearity (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f) (a : ℝ) :
    C(ℝ × Torus3 × ℝ, ℝ) :=
  ⟨fun p => f (a + p.1, p.2.1), by
    exact (Continuous.continuous_of_isSmoothOnSpaceTime hf).comp
      ((continuous_const.add continuous_fst).prodMk
        (continuous_fst.comp continuous_snd))⟩

open scoped ContDiff in
private theorem contDiff_nonlinLift_forcing {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (a : ℝ) :
    ContDiff ℝ ∞ (nonlinLift (forcingNonlinearity f hf a)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ((Fin 3 → ℝ) × ℝ) =>
    f (a + p.1, torusProj p.2.1))
  unfold IsSmoothOnSpaceTime at hf
  change ContDiff ℝ ∞ ((fun q : ℝ × (Fin 3 → ℝ) => f (q.1, torusProj q.2)) ∘
    fun p : ℝ × ((Fin 3 → ℝ) × ℝ) => (a + p.1, p.2.1))
  exact hf.comp ((contDiff_const.add contDiff_fst).prodMk
    (contDiff_fst.comp contDiff_snd))

open scoped ContDiff in
private theorem smooth_duhamel_shift {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (a T : ℝ) (hT : 0 ≤ T) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × (Fin 3 → ℝ) =>
        (PDE.duhamel (fun s => forcingPath f hf (a + s)) p.1)
          (torusProj p.2))
      (Ioo 0 T ×ˢ (Set.univ : Set (Fin 3 → ℝ))) := by
  let G := forcingNonlinearity f hf a
  let u : ℝ → C(Torus3, ℝ) := fun t => PDE.duhamel (fun s => forcingPath f hf (a + s)) t
  have hpath : Continuous (fun s => forcingPath f hf (a + s)) :=
    (continuous_forcingPath hf).comp (continuous_const.add continuous_id)
  have hu : Continuous u := PDE.continuous_duhamel hpath
  have hmild : PDE.IsMildSolution G 0 T u := by
    intro t ht
    change PDE.duhamel (fun s => forcingPath f hf (a + s)) t =
      PDE.heatOp t 0 + PDE.duhamel (fun s => PDE.nemytskii G s (u s)) t
    rw [PDE.heatOp_zero_right, zero_add]
    rfl
  have hs := PDE.contDiffOn_of_isMildSolution
    (contDiff_nonlinLift_forcing hf a) (by
      simp only [ContinuousMap.zero_apply]
      fun_prop) hT hu hmild
  exact hs

open scoped ContDiff in
private theorem smooth_duhamel_weighted_shift {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (a T : ℝ) (hT : 0 ≤ T) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × (Fin 3 → ℝ) =>
        (PDE.duhamel (fun s => exp (a + s) • forcingPath f hf (a + s)) p.1)
          (torusProj p.2))
      (Ioo 0 T ×ˢ (Set.univ : Set (Fin 3 → ℝ))) := by
  let f' : SpaceTime → ℝ := fun z => exp z.1 * f z
  have hf' : IsSmoothOnSpaceTime f' := by
    unfold IsSmoothOnSpaceTime at hf ⊢
    change ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      exp p.1 * f (p.1, torusProj p.2))
    exact (Real.contDiff_exp.comp contDiff_fst).mul hf
  have h := smooth_duhamel_shift hf' a T hT
  convert h using 1
  funext p
  congr 1

private theorem integrable_heatKernel_massive_forcing
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {C : ℝ} {q : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : SpaceTime, |f z| ≤ C * (1 + |z.1|) ^ q)
    {a r : ℝ} (hr : 0 < r) (x : Torus3) :
    Integrable (fun p : Torus3 × SpaceTime =>
      heatKernel r p.1 *
        (massiveHeatKernel ((a, x - p.1) - p.2) * f p.2))
      ((volume : Measure Torus3).prod (volume : Measure SpaceTime)) := by
  let f₀ : SpaceTime → ℝ := fun z => |f z|
  have hf₀ : Continuous f₀ := (Continuous.continuous_of_isSmoothOnSpaceTime hf).abs
  have hpast : ∀ b : ℝ,
      IntegrableOn (fun z : SpaceTime => exp z.1 * |f₀ z|)
        {z | z.1 ≤ b} := by
    intro b
    exact weighted_past_integrable_of_polynomial_time_bound hf₀.measurable hC q
      (fun z => by simpa only [f₀, abs_abs] using hb z) b
  have hpast_f : ∀ b : ℝ,
      IntegrableOn (fun z : SpaceTime => exp z.1 * |f z|)
        {z | z.1 ≤ b} := by
    intro b
    simpa only [f₀, abs_abs] using hpast b
  let H : SpaceTime → ℝ := fun z =>
    ∫ w : SpaceTime, massiveHeatKernel (z - w) * f₀ w
  have hHc : Continuous H := by
    exact continuous_massiveHeatKernel_convolution_of_weighted_past hf₀ hpast
  have hHy : Continuous (fun y : Torus3 => H (a, x - y)) :=
    hHc.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  obtain ⟨B, hB⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Torus3)).bddAbove_image hHy.continuousOn
  let D : ℝ := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  have hHD (y : Torus3) : H (a, x - y) ≤ D := by
    exact (hB ⟨y, mem_univ _, rfl⟩).trans (le_max_left _ _)
  let F : Torus3 × SpaceTime → ℝ := fun p =>
    heatKernel r p.1 * (massiveHeatKernel ((a, x - p.1) - p.2) * f p.2)
  have hFm : Measurable F := by
    have harg : Measurable (fun p : Torus3 × SpaceTime =>
        ((a, x - p.1) - p.2)) := by fun_prop
    exact ((measurable_heatKernel_fixed r).comp measurable_fst).mul
      ((measurable_massiveHeatKernel.comp harg).mul
        ((Continuous.continuous_of_isSmoothOnSpaceTime hf).measurable.comp measurable_snd))
  have hGint (y : Torus3) : Integrable
      (fun w : SpaceTime => massiveHeatKernel ((a, x - y) - w) * f w) := by
    exact integrable_massiveHeatKernel_product_of_weighted_past
      (Continuous.continuous_of_isSmoothOnSpaceTime hf) hpast_f (a, x - y)
  have hslice (y : Torus3) : Integrable (fun w : SpaceTime => F (y, w)) := by
    simpa only [F] using (hGint y).const_mul (heatKernel r y)
  apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
  have houter : Integrable (fun y : Torus3 => heatKernel r y * D) :=
    (integrable_heatKernel_fixed hr).mul_const D
  apply houter.mono'
    (hFm.aestronglyMeasurable.norm.integral_prod_right')
  filter_upwards [] with y
  have hnorm : ∫ w : SpaceTime, ‖F (y, w)‖ = heatKernel r y * H (a, x - y) := by
    calc
      ∫ w : SpaceTime, ‖F (y, w)‖ =
          ∫ w : SpaceTime, heatKernel r y *
            (massiveHeatKernel ((a, x - y) - w) * f₀ w) := by
        apply integral_congr_ae
        filter_upwards [] with w
        dsimp [F, f₀]
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hr y),
          abs_mul, abs_of_nonneg (massiveHeatKernel_nonneg _)]
      _ = heatKernel r y * H (a, x - y) := by
        rw [integral_const_mul]
  rw [Real.norm_of_nonneg (integral_nonneg fun w => norm_nonneg (F (y, w))), hnorm]
  exact mul_le_mul_of_nonneg_left (hHD y) (heatKernel_nonneg hr y)

private theorem heatKernel_weighted_potential_shift
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {C : ℝ} {q : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : SpaceTime, |f z| ≤ C * (1 + |z.1|) ^ q)
    {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : ∀ (t : ℝ) (x : Torus3),
      ψ t x = ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * f w)
    {a r : ℝ} (hr : 0 < r) (x : Torus3) :
    exp a * PDE.heatOp r (ψ a) x =
      ∫ w : SpaceTime,
        (if w.1 < a then exp w.1 * heatKernel (r + (a - w.1)) (x - w.2)
          else 0) * f w := by
  have hF := integrable_heatKernel_massive_forcing (a := a) hf hC hb hr x
  have hswap :
      (∫ y : Torus3, ∫ w : SpaceTime,
        heatKernel r y * (massiveHeatKernel ((a, x - y) - w) * f w)) =
        ∫ w : SpaceTime, ∫ y : Torus3,
          heatKernel r y * (massiveHeatKernel ((a, x - y) - w) * f w) :=
    integral_integral_swap hF
  calc
    exp a * PDE.heatOp r (ψ a) x =
        exp a * ∫ y : Torus3, heatKernel r y * ψ a (x - y) := by
      rw [PDE.heatOp_eq_heatSemigroup hr, heatSemigroup_eq_torus_integral hr]
    _ = exp a * ∫ y : Torus3, heatKernel r y *
        (∫ w : SpaceTime, massiveHeatKernel ((a, x - y) - w) * f w) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hψ]
    _ = exp a * ∫ y : Torus3, ∫ w : SpaceTime,
        heatKernel r y * (massiveHeatKernel ((a, x - y) - w) * f w) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← integral_const_mul]
    _ = exp a * ∫ w : SpaceTime, ∫ y : Torus3,
        heatKernel r y * (massiveHeatKernel ((a, x - y) - w) * f w) := by
      rw [hswap]
    _ = ∫ w : SpaceTime, exp a *
        (∫ y : Torus3, heatKernel r y *
          (massiveHeatKernel ((a, x - y) - w) * f w)) := by
      rw [← integral_const_mul]
    _ = ∫ w : SpaceTime, exp a *
        ((if w.1 < a then exp (-(a - w.1)) *
            heatKernel (r + (a - w.1)) (x - w.2) else 0) * f w) := by
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hw : w.1 < a
      · have hs : 0 < a - w.1 := sub_pos.mpr hw
        have harg (y : Torus3) :
            (a, x - y) - w = (a - w.1, (x - w.2) - y) := by
          apply Prod.ext
          · rfl
          · ext i
            change (x i - y i) - w.2 i = (x i - w.2 i) - y i
            abel
        have hfactor :
            (∫ y : Torus3, heatKernel r y *
                (massiveHeatKernel ((a, x - y) - w) * f w)) =
              (∫ y : Torus3, heatKernel r y *
                massiveHeatKernel ((a, x - y) - w)) * f w := by
          rw [← integral_mul_const]
          apply integral_congr_ae
          filter_upwards [] with y
          ring
        have hinner :
            (∫ y : Torus3, heatKernel r y *
                massiveHeatKernel ((a, x - y) - w)) =
              exp (-(a - w.1)) * heatKernel (r + (a - w.1)) (x - w.2) := by
          calc
            (∫ y : Torus3, heatKernel r y *
                massiveHeatKernel ((a, x - y) - w)) =
                ∫ y : Torus3, heatKernel r y *
                  massiveHeatKernel (a - w.1, (x - w.2) - y) := by
                    apply integral_congr_ae
                    filter_upwards [] with y
                    rw [harg]
            _ = exp (-(a - w.1)) * heatKernel (r + (a - w.1)) (x - w.2) :=
              integral_heatKernel_mul_massiveHeatKernel_torus hr hs _
        rw [hfactor, hinner]
        simp [hw]
      · have hzero (y : Torus3) :
            massiveHeatKernel ((a, x - y) - w) = 0 := by
          have htime : ¬0 < ((a, x - y) - w).1 := by
            change ¬0 < a - w.1
            exact not_lt.mpr (le_of_not_gt fun h => hw (by linarith))
          rw [massiveHeatKernel]
          exact ite_eq_right htime
        have hfactor :
            (∫ y : Torus3, heatKernel r y *
                (massiveHeatKernel ((a, x - y) - w) * f w)) = 0 := by
          calc
            (∫ y : Torus3, heatKernel r y *
                (massiveHeatKernel ((a, x - y) - w) * f w)) =
                ∫ y : Torus3, 0 := by
                  apply integral_congr_ae
                  filter_upwards [] with y
                  rw [hzero y, zero_mul, mul_zero]
            _ = 0 := by simp
        rw [hfactor]
        simp [hw]
    _ = ∫ w : SpaceTime,
        (if w.1 < a then exp w.1 * heatKernel (r + (a - w.1))
            (x - w.2) else 0) * f w := by
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hw : w.1 < a
      · have hifInner :
            (if w.1 < a then exp (-(a - w.1)) *
                heatKernel (r + (a - w.1)) (x - w.2) else 0) =
              exp (-(a - w.1)) * heatKernel (r + (a - w.1)) (x - w.2) :=
          ite_eq_left hw
        have hif :
            (if w.1 < a then exp w.1 * heatKernel (r + (a - w.1))
                (x - w.2) else 0) =
              exp w.1 * heatKernel (r + (a - w.1)) (x - w.2) :=
          ite_eq_left hw
        rw [hifInner, hif]
        calc
          exp a * (exp (-(a - w.1)) * heatKernel (r + (a - w.1))
              (x - w.2) * f w) =
              (exp a * exp (-(a - w.1))) *
                (heatKernel (r + (a - w.1)) (x - w.2) * f w) := by ring
          _ = exp w.1 * heatKernel (r + (a - w.1)) (x - w.2) * f w := by
            have hexp : exp a * exp (-(a - w.1)) = exp w.1 := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [hexp]
            ring
      · have hif :
            (if w.1 < a then exp w.1 * heatKernel (r + (a - w.1))
                (x - w.2) else 0) = 0 := ite_eq_right hw
        have hifInner :
            (if w.1 < a then exp (-(a - w.1)) *
                heatKernel (r + (a - w.1)) (x - w.2) else 0) = 0 :=
          ite_eq_right hw
        rw [hifInner, hif]
        simp

private theorem duhamel_weighted_shift
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {a r : ℝ} (_hr : 0 < r) (x : Torus3) :
    PDE.duhamel (fun s => exp (a + s) • forcingPath f hf (a + s)) r x =
      ∫ s in (0 : ℝ)..r,
        (if 0 < r - s then
            ∫ y : Torus3, heatKernel (r - s) y *
              (exp (a + s) * f (a + s, x - y))
          else (exp (a + s) • forcingPath f hf (a + s)) x) := by
  have hpath : Continuous (fun s => exp (a + s) • forcingPath f hf (a + s)) := by
    exact (continuous_exp.comp (continuous_const.add continuous_id)).smul
      ((continuous_forcingPath hf).comp (continuous_const.add continuous_id))
  rw [PDE.duhamel_apply hpath]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp
  by_cases hsr : 0 < r - s
  · rw [ite_eq_left hsr]
    rw [PDE.heatOp_eq_heatSemigroup hsr,
      heatSemigroup_eq_torus_integral hsr]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [forcingPath, ContinuousMap.smul_apply, smul_eq_mul]
  · rw [ite_eq_right hsr, PDE.heatOp_of_nonpos (le_of_not_gt hsr)]
    simp [ContinuousMap.smul_apply, smul_eq_mul]

private theorem recent_weighted_shift
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hψi : ∀ (t : ℝ) (x : Torus3), Integrable
      (fun w : SpaceTime => massiveHeatKernel ((t, x) - w) * f w))
    {a r : ℝ} (hr : 0 < r) (x : Torus3) :
    (∫ s in (0 : ℝ)..r,
      (if 0 < r - s then
          ∫ y : Torus3, heatKernel (r - s) y *
            (exp (a + s) * f (a + s, x - y))
        else (exp (a + s) • forcingPath f hf (a + s)) x)) =
      ∫ w in Ioc a (a + r) ×ˢ (Set.univ : Set Torus3),
        exp (a + r) * (massiveHeatKernel ((a + r, x) - w) * f w) := by
  let S : Set ℝ := Ioc a (a + r)
  let R : Set SpaceTime := S ×ˢ (Set.univ : Set Torus3)
  let F : SpaceTime → ℝ := fun w =>
    exp (a + r) * (massiveHeatKernel ((a + r, x) - w) * f w)
  let F₂ : ℝ × Torus3 → ℝ := fun w =>
    S.indicator (fun s =>
      exp (a + r) *
        (massiveHeatKernel ((a + r, x) - (s, w.2)) * f (s, w.2))) w.1
  have hS : MeasurableSet S := measurableSet_Ioc
  have hR : MeasurableSet R := hS.prod MeasurableSet.univ
  have hF : Integrable F := by
    simpa only [F] using (hψi (a + r) x).const_mul (exp (a + r))
  have hEq : F₂ = R.indicator F := by
    funext w
    rcases w with ⟨t, y⟩
    by_cases hw : t ∈ S
    · simp [F₂, F, R, hw]
    · simp [F₂, F, R, hw]
  have hF₂ : Integrable F₂ := by
    rw [hEq]
    exact hF.integrableOn.integrable_indicator hR
  have hprod : ∫ w : SpaceTime, R.indicator F w =
      ∫ s : ℝ, ∫ y : Torus3, F₂ (s, y) := by
    rw [← hEq]
    exact integral_prod F₂ hF₂
  have hset : ∫ w in R, F w = ∫ s : ℝ, ∫ y : Torus3, F₂ (s, y) := by
    rw [← integral_indicator hR]
    exact hprod
  let g : ℝ → ℝ := fun s => ∫ y : Torus3, F₂ (s, y)
  have hgzero : ∀ s ∉ S, g s = 0 := by
    intro s hs
    simp only [g, F₂, indicator_of_notMem hs]
    simp
  have hset' : ∫ s in S, g s = ∫ s : ℝ, g s := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [] with s
    by_cases hs : s ∈ S
    · simp [hs]
    · simp [hgzero s hs, hs]
  have hpoint : ∀ s ∈ Ioo (0 : ℝ) r, g (a + s) =
      (if 0 < r - s then
          ∫ y : Torus3, heatKernel (r - s) y *
            (exp (a + s) * f (a + s, x - y))
        else (exp (a + s) • forcingPath f hf (a + s)) x) := by
    intro s hs
    have hslt : s < r := hs.2
    have hsr : 0 < r - s := sub_pos.mpr hslt
    have hsa : a + s ∈ S := by
      constructor <;> linarith [hs.1, hs.2]
    let _ : (volume : Measure Torus3).IsNegInvariant :=
      Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
    have htrans := integral_sub_left_eq_self
      (μ := (volume : Measure Torus3))
      (fun y : Torus3 => F₂ (a + s, y)) x
    have hF₂_right : ∀ y : Torus3,
        F₂ (a + s, x - y) = heatKernel (r - s) y *
          (exp (a + s) * f (a + s, x - y)) := by
      intro y
      have htime : (a + r, x) - (a + s, x - y) = (r - s, y) := by
        apply Prod.ext
        · dsimp
          ring
        · change x - (x - y) = y
          abel
      rw [show F₂ (a + s, x - y) =
          exp (a + r) *
            (massiveHeatKernel ((a + r, x) - (a + s, x - y)) *
              f (a + s, x - y)) by
        simp only [F₂, indicator_of_mem hsa]]
      rw [htime]
      simp only [massiveHeatKernel, hsr, ite_true]
      have hexp : exp (a + r) * exp (-(r - s)) = exp (a + s) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        exp (a + r) * (exp (-(r - s)) * heatKernel (r - s) y *
            f (a + s, x - y)) =
            (exp (a + r) * exp (-(r - s))) *
              (heatKernel (r - s) y * f (a + s, x - y)) := by ring
        _ = exp (a + s) * (heatKernel (r - s) y * f (a + s, x - y)) := by
          rw [hexp]
        _ = heatKernel (r - s) y *
            (exp (a + s) * f (a + s, x - y)) := by ring
    rw [ite_eq_left hsr]
    calc
      g (a + s) = ∫ y : Torus3, F₂ (a + s, y) := rfl
      _ = ∫ y : Torus3, F₂ (a + s, x - y) := by
        simpa using htrans.symm
      _ = ∫ y : Torus3, heatKernel (r - s) y *
          (exp (a + s) * f (a + s, x - y)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hF₂_right
  calc
    (∫ s in (0 : ℝ)..r,
        (if 0 < r - s then
            ∫ y : Torus3, heatKernel (r - s) y *
              (exp (a + s) * f (a + s, x - y))
          else (exp (a + s) • forcingPath f hf (a + s)) x)) =
        ∫ s in (0 : ℝ)..r, g (a + s) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume r] with s hne
      intro hs
      rw [uIoc_of_le hr.le] at hs
      exact (hpoint s ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩).symm
    _ = ∫ s in (a : ℝ)..(a + r), g s := by
      simpa only [add_comm, zero_add, add_zero] using
        (intervalIntegral.integral_comp_add_right (f := g) (a := (0 : ℝ)) (b := r) a)
    _ = ∫ s in S, g s := by
      rw [intervalIntegral.integral_of_le (by linarith : a ≤ a + r)]
    _ = ∫ s : ℝ, g s := hset'
    _ = ∫ w in R, F w := hset.symm

private theorem weighted_potential_mild_identity
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {C : ℝ} {q : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : SpaceTime, |f z| ≤ C * (1 + |z.1|) ^ q)
    {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : ∀ (t : ℝ) (x : Torus3),
      ψ t x = ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * f w)
    (hψi : ∀ (t : ℝ) (x : Torus3), Integrable
      (fun w : SpaceTime => massiveHeatKernel ((t, x) - w) * f w))
    {a r : ℝ} (hr : 0 < r) (x : Torus3) :
    exp (a + r) * ψ (a + r) x =
      exp a * PDE.heatOp r (ψ a) x +
        PDE.duhamel (fun s => exp (a + s) • forcingPath f hf (a + s)) r x := by
  let A : Set SpaceTime := {w | w.1 < a}
  let R : Set SpaceTime := Ioc a (a + r) ×ˢ (Set.univ : Set Torus3)
  let F : SpaceTime → ℝ := fun w =>
    exp (a + r) * (massiveHeatKernel ((a + r, x) - w) * f w)
  have hA : MeasurableSet A := measurableSet_lt measurable_fst measurable_const
  have hR : MeasurableSet R := measurableSet_Ioc.prod MeasurableSet.univ
  have hF : Integrable F := by
    simpa only [F] using (hψi (a + r) x).const_mul (exp (a + r))
  have hpast :
      (∫ w : SpaceTime,
        (if w.1 < a then exp w.1 * heatKernel (r + (a - w.1))
            (x - w.2) else 0) * f w) = ∫ w in A, F w := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hw : w.1 < a
    · have htime : 0 < r + (a - w.1) := by linarith
      have harg : (a + r, x) - w =
          (r + (a - w.1), x - w.2) := by
        apply Prod.ext
        · dsimp
          ring
        · rfl
      have hexp : exp (a + r) * exp (-(r + (a - w.1))) = exp w.1 := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [indicator_of_mem (show w ∈ A from hw), ite_eq_left hw]
      change (exp w.1 * heatKernel (r + (a - w.1)) (x - w.2)) * f w =
        exp (a + r) * (massiveHeatKernel ((a + r, x) - w) * f w)
      rw [harg, massiveHeatKernel]
      simp only [htime, ite_true]
      calc
        (exp w.1 * heatKernel (r + (a - w.1)) (x - w.2)) * f w =
            (exp (a + r) * exp (-(r + (a - w.1))) *
            heatKernel (r + (a - w.1)) (x - w.2)) * f w := by rw [hexp]
        _ = exp (a + r) *
            (exp (-(r + (a - w.1))) * heatKernel (r + (a - w.1))
              (x - w.2) * f w) := by ring
    · simp [A, hw]
  have hae : ∀ᵐ w : SpaceTime ∂volume, w.1 ≠ a := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_preimage measurable_fst (measurableSet_singleton a)).compl)).2
    filter_upwards [@Measure.ae_ne ℝ _ volume
      (Measure.IsAddHaarMeasure.nullSingletonClass volume) a] with t ht
    exact ae_of_all _ (fun _ => ht)
  have hcomp : ∫ w in Aᶜ, F w = ∫ w in R, F w := by
    rw [← integral_indicator hA.compl, ← integral_indicator hR]
    apply integral_congr_ae
    filter_upwards [hae] with w hwa
    by_cases hw : w.1 < a
    · have hnotA : w ∉ Aᶜ := by simp [A, hw]
      have hnotR : w ∉ R := by
        intro h
        exact (not_lt_of_ge h.1.1.le) hw
      rw [indicator_of_notMem hnotA, indicator_of_notMem hnotR]
    · by_cases ht : w.1 ≤ a + r
      · have hwR : w ∈ R :=
          ⟨⟨lt_of_le_of_ne (le_of_not_gt hw) (Ne.symm hwa), ht⟩, mem_univ _⟩
        have hwAc : w ∈ Aᶜ := by simp [A, hw]
        rw [indicator_of_mem hwAc, indicator_of_mem hwR]
      · have hzero : massiveHeatKernel ((a + r, x) - w) = 0 := by
          rw [massiveHeatKernel]
          apply ite_eq_right
          change ¬0 < a + r - w.1
          linarith
        have hwAc : w ∈ Aᶜ := by simp [A, hw]
        have hwR : w ∉ R := by simp [R, ht]
        rw [indicator_of_mem hwAc, indicator_of_notMem hwR]
        simp [F, hzero]
  have hpast' := heatKernel_weighted_potential_shift (a := a) (r := r) hf hC hb hψ hr x
  have hrecent := recent_weighted_shift (a := a) (r := r) hf hψi hr x
  calc
    exp (a + r) * ψ (a + r) x =
        exp (a + r) * ∫ w : SpaceTime,
          massiveHeatKernel ((a + r, x) - w) * f w := by rw [hψ]
    _ = ∫ w : SpaceTime, F w := by
      rw [integral_const_mul]
    _ = (∫ w in A, F w) + ∫ w in Aᶜ, F w := by
      rw [← integral_add_compl (μ := (volume : Measure SpaceTime)) hA hF]
    _ = (∫ w in A, F w) + ∫ w in R, F w := by
      rw [hcomp]
    _ = (∫ w : SpaceTime,
          (if w.1 < a then exp w.1 * heatKernel (r + (a - w.1))
              (x - w.2) else 0) * f w) + ∫ w in R, F w := by rw [hpast]
    _ = exp a * PDE.heatOp r (ψ a) x +
          PDE.duhamel (fun s => exp (a + s) • forcingPath f hf (a + s)) r x := by
      have hduh := duhamel_weighted_shift hf (a := a) (r := r) hr x
      rw [hpast', hduh, hrecent]

open scoped ContDiff in
theorem massivePotential_exists_smooth_of_polynomialLift_growth
    (f : SpaceTime → ℝ)
    (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) :
    ∃ ψ : ℝ → C(Torus3, ℝ),
      RegularityStructures.IsMassivePotential f ψ ∧
      IsSmoothOnSpaceTime (fun z : SpaceTime => ψ z.1 z.2) ∧
      Continuous ψ := by
  obtain ⟨ψ, hψ⟩ := massivePotential_exists_of_polynomialLift_growth f hf hg
  obtain ⟨Cg, q, hg'⟩ := hg
  have hzero : ∀ z : ParabolicSpace, |f (z.1, torusProj z.2)| ≤
      Cg * (1 + parabolicNorm z) ^ q := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hg' 0 (by norm_num)
  obtain ⟨C, hC, hb⟩ := polynomial_time_bound_of_polynomialLift_growth hzero
  have hfc : Continuous f := Continuous.continuous_of_isSmoothOnSpaceTime hf
  have hψi : ∀ (t : ℝ) (x : Torus3), Integrable
      (fun w : SpaceTime => massiveHeatKernel ((t, x) - w) * f w) := by
    intro t x
    exact integrable_massiveHeatKernel_product_of_weighted_past hfc
      (fun a => weighted_past_integrable_of_polynomial_time_bound hfc.measurable hC q hb a)
      (t, x)
  have hψcont : Continuous ψ := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hc := continuous_massiveHeatKernel_convolution_of_weighted_past hfc
      (fun a => weighted_past_integrable_of_polynomial_time_bound hfc.measurable hC q hb a)
    have hc' := hc.comp (continuous_fst.prodMk continuous_snd)
    apply hc'.congr
    intro p
    exact (hψ p.1 p.2).symm
  have hpot : RegularityStructures.IsMassivePotential f ψ := ⟨hψi, hψ⟩
  have hsm : IsSmoothOnSpaceTime (fun z : SpaceTime => ψ z.1 z.2) := by
    unfold IsSmoothOnSpaceTime
    rw [contDiff_iff_contDiffAt]
    intro p
    let a : ℝ := p.1 - 1
    let D : Set ParabolicSpace := Ioo (0 : ℝ) 2 ×ˢ (Set.univ : Set (Fin 3 → ℝ))
    let q₀ : ParabolicSpace := (p.1 - a, p.2)
    have hq₀ : q₀ ∈ D := by
      exact ⟨⟨by simp [q₀, a], by simp [q₀, a]⟩, mem_univ _⟩
    let V : ParabolicSpace → ℝ := fun z =>
      exp (a + z.1) * ψ (a + z.1) (torusProj z.2)
    have hheat : ContDiffOn ℝ ∞ (fun z : ParabolicSpace =>
        exp a * heatOp z.1 (ψ a) (torusProj z.2)) D := by
      have hheat0 := Datum.smoothPos_heatField (ψ a)
      have hpos0 : ContDiffOn ℝ ∞ (Datum.heatField (ψ a)) Datum.posTime := hheat0
      have hpos : ContDiffOn ℝ ∞ (fun z : ParabolicSpace =>
          Datum.heatField (ψ a) z) D := hpos0.mono (fun z hz => hz.1.1)
      have hpos' : ContDiffOn ℝ ∞ (fun z : ParabolicSpace =>
          heatOp z.1 (ψ a) (torusProj z.2)) D := by
        apply hpos.congr
        intro z hz
        exact (Datum.heatField_of_pos (ψ a) hz.1.1).symm
      simpa only [smul_eq_mul] using hpos'.const_smul (exp a)
    have hduh : ContDiffOn ℝ ∞ (fun z : ParabolicSpace =>
        PDE.duhamel (fun s => exp (a + s) • forcingPath f hf (a + s)) z.1
          (torusProj z.2)) D := by
      exact smooth_duhamel_weighted_shift hf a 2 (by norm_num)
    have hV : ContDiffOn ℝ ∞ V D := by
      apply (hheat.add hduh).congr
      intro z hz
      have hm := weighted_potential_mild_identity (a := a) (r := z.1) hf hC hb hψ hψi
        hz.1.1
        (torusProj z.2)
      exact hm
    have hVq : ContDiffAt ℝ ∞ V q₀ :=
      hV.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq₀)
    have hq : ContDiffAt ℝ ∞ (fun z : ParabolicSpace =>
        (z.1 - a, z.2)) p :=
      (contDiff_fst.sub contDiff_const).prodMk contDiff_snd |>.contDiffAt
    have hVorig : ContDiffAt ℝ ∞ (fun z : ParabolicSpace =>
        exp z.1 * ψ z.1 (torusProj z.2)) p := by
      have hcomp := hVq.comp p hq
      convert hcomp using 1
      funext z
      simp only [Function.comp_apply, V]
      have hz : a + (z.1 - a) = z.1 := by ring
      rw [hz]
    have hexp : ContDiffAt ℝ ∞ (fun z : ParabolicSpace => exp (-z.1)) p :=
      (Real.contDiff_exp.comp contDiff_fst.neg).contDiffAt
    have hmul := hexp.mul hVorig
    simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, exp_zero, one_mul] using hmul
  exact ⟨ψ, hpot, hsm, hψcont⟩


end RegularityStructures.Phi43

end
