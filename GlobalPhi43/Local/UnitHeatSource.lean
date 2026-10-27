/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.RadiusGeometry
public import GlobalPhi43.Local.FixedHeatCutoff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! A fixed finite past source box and the exact original field allowance. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric Filter Topology MeasureTheory

 def unitHeatSourceDomain : Set ParabolicSpace := ball 0 1 ∩ {q | q.1 < 0}
 def unitHeatPastCarrier : Set ParabolicSpace := closedBall 0 1 ∩ {q | q.1 ≤ 0}
 def unitHeatSourceMeasure : Measure ParabolicSpace := volume.restrict unitHeatSourceDomain

 theorem unitHeatSourceDomain_measurable : MeasurableSet unitHeatSourceDomain :=
  (isOpen_ball.inter (isOpen_lt continuous_fst continuous_const)).measurableSet

 theorem unitHeatPastCarrier_isCompact : IsCompact unitHeatPastCarrier :=
  (isCompact_closedBall (0 : ParabolicSpace) 1).inter_right (isClosed_le continuous_fst continuous_const)

 theorem unitHeatSourceDomain_subset_carrier : unitHeatSourceDomain ⊆ unitHeatPastCarrier := by
  intro q hq
  refine ⟨ball_subset_closedBall hq.1, ?_⟩
  change q.1 ≤ 0
  have ht : q.1 < 0 := hq.2
  exact ht.le

 instance unitHeatSourceMeasure_isFinite : IsFiniteMeasure unitHeatSourceMeasure where
  measure_univ_lt_top := by
    rw [unitHeatSourceMeasure, Measure.restrict_apply_univ]
    exact (measure_mono unitHeatSourceDomain_subset_carrier).trans_lt unitHeatPastCarrier_isCompact.measure_lt_top

 theorem unitHeatSourceMeasure_ae_domain : ∀ᵐ q ∂unitHeatSourceMeasure, q ∈ unitHeatSourceDomain :=
  ae_restrict_mem unitHeatSourceDomain_measurable

 theorem unitHeatSourceDomain_subset_pastBall : unitHeatSourceDomain ⊆ pastBall 0 1 := by
  intro q hq
  have hn : ‖q‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hq.1
  have ht : |q.1| < 1 := by
    have hb : ‖q.1‖ ≤ ‖q‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    simpa only [Real.norm_eq_abs] using hb.trans_lt hn
  have hx : ‖q.2‖ < 1 := by
    have hb : ‖q.2‖ ≤ ‖q‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    exact hb.trans_lt hn
  constructor
  · change max (Real.sqrt |(0 : ℝ) - q.1|) ‖(0 : Fin 3 → ℝ) - q.2‖ < 1
    apply max_lt
    · apply (Real.sqrt_lt (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2
      simpa only [zero_sub, abs_neg, one_pow] using ht
    · simpa only [zero_sub, norm_neg] using hx
  · exact hq.2

 theorem unit_source_extension_bound {h g : ParabolicSpace → ℝ} {H : ℝ}
    (he : ∀ p ∈ unitHeatPastCarrier, g =ᶠ[𝓝 p] h)
    (hbound : ∀ p ∈ pastBall (0 : ParabolicSpace) 1, |h p| ≤ H) :
    ∀ᵐ q ∂unitHeatSourceMeasure, |g q| ≤ H := by
  filter_upwards [unitHeatSourceMeasure_ae_domain] with q hq
  rw [(he q (unitHeatSourceDomain_subset_carrier hq)).self_of_nhds]
  exact hbound q (unitHeatSourceDomain_subset_pastBall hq)

end GlobalPhi43.Local
