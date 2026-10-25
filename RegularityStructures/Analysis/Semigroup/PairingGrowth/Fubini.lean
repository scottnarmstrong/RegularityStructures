/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Swap
public import RegularityStructures.Analysis.Semigroup.Pairing.Fubini

/-!
# Fubini integrability against a distribution with growth (`LocalBall` version)

Adaptation of `RegularityStructures.Analysis.Semigroup.Pairing.Fubini` to `LocalBall`.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}
  {lam : ℝ}

theorem LocalBall.exists_integral_norm_mul_apply_le [SFinite μ] (hK : K.IsSymmetric) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalBall Λ x₀ γ A C lam) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) {φ : E → ℝ} 
    (hφ : K.IsSupported φ x₀ lam) (h₀ : ℝ) :
    ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀,
      ∫ z, ‖Λ s z * K.apply v φ z‖ ∂μ ≤ W * ∫ y, ‖φ y‖ ∂μ := by
  obtain ⟨W, -, hW⟩ := hΛ.exists_integral_norm_le hs hφ.supp h₀
  refine ⟨W, fun v hv => ?_⟩
  have hint := hΛ.integrable_prod hs hφ hv.1
  calc ∫ z, ‖Λ s z * K.apply v φ z‖ ∂μ
      ≤ ∫ z, ∫ y, ‖K.kernel v y z * Λ s z * φ y‖ ∂μ ∂μ := by
        refine integral_mono (hΛ.integrable_mul_apply hK hs hφ hv.1).norm
          hint.norm.swap.integral_prod_left fun z => ?_
        have e : Λ s z * K.apply v φ z = ∫ y, K.kernel v y z * Λ s z * φ y ∂μ := by
          simp only [apply]
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [hK v y z]; ring
        rw [e]
        exact norm_integral_le_integral_norm _
    _ = ∫ y, ∫ z, ‖K.kernel v y z * Λ s z * φ y‖ ∂μ ∂μ :=
        (integral_integral_swap (f := fun y z => ‖K.kernel v y z * Λ s z * φ y‖) hint.norm).symm
    _ ≤ ∫ y, W * ‖φ y‖ ∂μ := by
        refine integral_mono hint.norm.integral_prod_left (hφ.integrable.norm.const_mul W)
          fun y => ?_
        have := hW v hv y
        rwa [← Real.norm_eq_abs (φ y)] at this
    _ = W * ∫ y, ‖φ y‖ ∂μ := integral_const_mul _ _

theorem LocalBall.integrable_uncurry_apply [SFinite μ] (hK : K.IsSymmetric) (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ}
    {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalBall Λ x₀ γ A C lam) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    {ψ : E → ℝ}  (hψ : K.IsSupported ψ x₀ lam) (h : ℝ) :
    Integrable (Function.uncurry fun (v : ℝ) (z : E) => Λ s z * K.apply v ψ z)
      ((volume.restrict (Set.Ioc 0 h)).prod μ) := by
  have hm : Measurable (Function.uncurry fun (v : ℝ) (z : E) => Λ s z * K.apply v ψ z) :=
    ((hΛ.meas s hs.1).comp measurable_snd).mul (measurable_apply_uncurry hJ hψ.meas)
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  obtain ⟨W, hW⟩ := hΛ.exists_integral_norm_mul_apply_le hK hs hψ h
  refine ⟨(ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv =>
      hΛ.integrable_mul_apply hK hs hψ hv.1), ?_⟩
  refine Integrable.mono' (integrable_const (W * ∫ y, ‖ψ y‖ ∂μ))
    hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => ?_))
  have hnn : 0 ≤ ∫ z, ‖Λ s z * K.apply v ψ z‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  change ‖∫ z, ‖Λ s z * K.apply v ψ z‖ ∂μ‖ ≤ _
  rw [Real.norm_of_nonneg hnn]
  exact hW v hv

end RegularityStructures.RegularisingSemigroup

end
