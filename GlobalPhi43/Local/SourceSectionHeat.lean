/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.TimeFreeGeometry
public import GlobalPhi43.Local.InfiniteKernelPast
public import GlobalPhi43.Local.CompactSectionBounds
public import GlobalPhi43.MW20.LocalHeatAverage
public import GlobalPhi43.MW20.LocalAverageRegularity
public import GlobalPhi43.MW20.CompactKernelTube

/-! Actual heat commutation on the local cylinder. No extension of the
germ outside the source cylinder, or future PDE assumption, is needed. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set Filter Topology
open scoped ContDiff

/-- The original local smoothness supplies C² germs of the section on
closure(D), including its upper time face. -/
theorem source_section_contDiffAt_two (U : GermPoint → ℝ) {r : ℝ}
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    {x y : ParabolicSpace} (hx : x ∈ closure (sourceCylinder r))
    (hy : y ∈ closure (sourceCylinder r)) : ContDiffAt ℝ 2 (fun z => U (x, z)) y := by
  obtain ⟨O, hO, hKO, hs⟩ := hU
  have hp : (x, y) ∈ O := hKO ⟨hx, hy⟩
  have hh : ContDiffAt ℝ 2 U (x, y) := (hs.contDiffAt (hO.mem_nhds hp)).of_le (by norm_num)
  exact hh.comp y (contDiffAt_const.prodMk contDiffAt_id)

/-- A compact testing tube exists inside the ACTUAL D_r for every legal
past ball and kernel scale. Its neighbourhood is constructed, not assumed. -/
theorem exists_source_section_testing_tube (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {r d L T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hLT : L + T ≤ d)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (hy : y ∈ pastBall x L) :
    ∃ δ > 0, ∀ᵐ w ∂infiniteKernelMeasure Φ hΦ T hT,
      ∀ z ∈ Metric.ball y δ, z + w ∈ closure (sourceCylinder r) := by
  have hc := (infiniteKernel_hasCompactSupport Φ hΦ hT hT₁).isCompact
  have hp : ∀ w ∈ tsupport (infiniteKernel Φ hΦ T hT), y + w ∈ sourceCylinder r := by
    intro w hw
    obtain ⟨ht, hdw⟩ := infiniteKernel_tsupport_closedPast Φ hΦ hT hT₁ hw
    have he := add_mem_pastBall_add hy ht hdw
    exact cylinderInterior_mem_domain (by norm_num : (0 : ℝ) ≤ 0)
      (pastBall_subset_interior (by norm_num) (by linarith) (by linarith) hx he)
  have hev : ∀ᶠ z in 𝓝 y, ∀ w ∈ tsupport (infiniteKernel Φ hΦ T hT), z + w ∈ sourceCylinder r := by
    apply hc.eventually_forall_of_forall_eventually
    intro w hw
    exact (continuous_fst.add continuous_snd).continuousAt.preimage_mem_nhds
      ((isOpen_sourceCylinder r).mem_nhds (hp w hw))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [infiniteKernelMeasure_ae_tsupport Φ hΦ hT] with w hw
  exact fun z hz => subset_closure (hball hz w hw)

/-- Commutation and C² regularity of the actual smoothed section on every
licensed past ball. All regularity and integrability are derived locally. -/
theorem source_section_heat_smoothing (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (U : GermPoint → ℝ) {r d L T : ℝ} (hr : 0 ≤ r)
    (hT : 0 < T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hLT : L + T ≤ d)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (hy : y ∈ pastBall x L) :
    sourceHeat (fun z => ∫ w, U (x, z + w) ∂infiniteKernelMeasure Φ hΦ T hT) y =
      ∫ w, sourceHeat (fun z => U (x, z)) (y + w) ∂infiniteKernelMeasure Φ hΦ T hT ∧
    ContDiffAt ℝ 2 (fun z => ∫ w, U (x, z + w) ∂infiniteKernelMeasure Φ hΦ T hT) y := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT₁
  have hd : 0 ≤ d := by linarith
  have hxD := subset_closure (cylinderInterior_mem_domain hd hx)
  obtain ⟨δ, hδ, htest⟩ := exists_source_section_testing_tube Φ hΦ hT hT₁ hL hLT hx hy
  have hf := fun z hz => source_section_contDiffAt_two U hU hxD (y := z) hz
  exact ⟨sourceHeat_local_average _ (fun z => U (x, z)) (isCompact_closure_sourceCylinder hr)
      Metric.isOpen_ball hf htest (Metric.mem_ball_self hδ),
    contDiffAt_average_on_open_two _ (fun z => U (x, z)) (isCompact_closure_sourceCylinder hr)
      Metric.isOpen_ball hf htest (Metric.mem_ball_self hδ)⟩

end GlobalPhi43.Local
