/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.KernelWeightedIntegrability

/-! A fixed compact coefficient costs only the original bounded source
size. Its bound is selected before the source or restricted measure. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory

 theorem exists_compact_coefficient_source_bound {a : ParabolicSpace → ℝ}
    (ha : Continuous a) (hca : HasCompactSupport a) :
    ∃ A ≥ 0, ∀ (μ : Measure ParabolicSpace), IsFiniteMeasure μ →
      ∀ (g : ParabolicSpace → ℝ) (H : ℝ), AEStronglyMeasurable g μ →
      (∀ᵐ q ∂μ, |g q| ≤ H) →
      Integrable (fun q => a q * g q) μ ∧
        (∫ q, |a q * g q| ∂μ) ≤ A * H * μ.real Set.univ := by
  obtain ⟨B, hB⟩ := ha.bounded_above_of_compact_support hca
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro μ hμ g H hg hbound
  have : IsFiniteMeasure μ := hμ
  have hA : 0 ≤ max 0 B := le_max_left _ _
  have hpoint : ∀ᵐ q ∂μ, ‖a q * g q‖ ≤ max 0 B * H := by
    filter_upwards [hbound] with q hq
    rw [norm_mul]
    have hgq : ‖g q‖ ≤ H := by simpa only [Real.norm_eq_abs] using hq
    exact mul_le_mul ((hB q).trans (le_max_right _ _)) hgq (norm_nonneg _) hA
  have hi : Integrable (fun q => a q * g q) μ :=
    (integrable_const (max 0 B * H)).mono' (ha.aestronglyMeasurable.mul hg) hpoint
  refine ⟨hi, ?_⟩
  have hh : (∫ q, |a q * g q| ∂μ) ≤ ∫ _ : ParabolicSpace, max 0 B * H ∂μ := by
    apply integral_mono_ae hi.abs (integrable_const _)
    filter_upwards [hpoint] with q hq
    change |a q * g q| ≤ max 0 B * H
    simpa only [Real.norm_eq_abs] using hq
  simpa only [integral_const, smul_eq_mul, mul_comm] using hh

end GlobalPhi43.Local
