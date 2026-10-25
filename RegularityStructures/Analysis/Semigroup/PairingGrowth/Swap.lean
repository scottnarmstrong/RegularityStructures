/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Kernel
public import RegularityStructures.Analysis.Semigroup.Pairing.Swap

/-!
# Self-adjointness against a distribution with growth (`LocalBall` version)

Adaptation of `RegularityStructures.Analysis.Semigroup.Pairing.Swap` to `LocalBall`.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}
  {lam : ℝ}

/-- Pointwise bound `∫ ‖Q_v(y, z) Λ_s(z) φ(y)‖ dz ≤ W |φ(y)|`, uniform in `v ≤ h₀`. -/
theorem LocalBall.exists_integral_norm_le {Λ : ℝ → E → ℝ} {x₀ : E}
    {γ : ℝ} {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalBall Λ x₀ γ A C lam) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) {φ : E → ℝ} 
    (hsupp : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (h₀ : ℝ) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y,
      ∫ z, ‖K.kernel v y z * Λ s z * φ y‖ ∂μ ≤ W * |φ y| := by
  obtain ⟨W, hW⟩ := hΛ.kernel_int _ hs h₀
  refine ⟨|W|, abs_nonneg _, fun v hv y => ?_⟩
  have e : ∫ z, ‖K.kernel v y z * Λ s z * φ y‖ ∂μ =
      (∫ z, |K.kernel v y z| * |Λ s z| ∂μ) * |φ y| := by
    rw [← integral_mul_const]
    simp only [Real.norm_eq_abs, abs_mul]
  rw [e]
  by_cases hy : K.scaleDist y x₀ ≤ lam
  · exact mul_le_mul_of_nonneg_right ((hW v hv y hy).trans (le_abs_self W)) (abs_nonneg _)
  · rw [hsupp y (not_le.1 hy)]; simp

theorem LocalBall.integrable_prod [SFinite μ] {Λ : ℝ → E → ℝ} {x₀ : E}
    {γ : ℝ} {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalBall Λ x₀ γ A C lam) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) {φ : E → ℝ}  (hφ : K.IsSupported φ x₀ lam) {h : ℝ}
    (hh : 0 < h) :
    Integrable (fun p : E × E => K.kernel h p.1 p.2 * Λ s p.2 * φ p.1) (μ.prod μ) := by
  have hmeas : Measurable (fun p : E × E => K.kernel h p.1 p.2 * Λ s p.2 * φ p.1) :=
    ((K.measurable_kernel h).mul ((hΛ.meas s hs.1).comp measurable_snd)).mul
      (hφ.meas.comp measurable_fst)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  · exact (K.integrable_kernel_mul hΛ.mem hh hs.1 y).mul_const (φ y)
  · obtain ⟨W, -, hW⟩ := hΛ.exists_integral_norm_le hs hφ.supp h
    refine Integrable.mono' (hφ.integrable.norm.const_mul W)
      hmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have hnn : 0 ≤ ∫ z, ‖K.kernel h y z * Λ s z * φ y‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    exact (hW h ⟨hh, le_rfl⟩ y).trans (le_of_eq (by rw [Real.norm_eq_abs]))

theorem LocalBall.integrable_mul {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalBall Λ x₀ γ A C lam) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) {φ : E → ℝ} 
    (hφ : K.IsSupported φ x₀ lam) : Integrable (fun y => Λ s y * φ y) μ := by
  refine Integrable.mono' (hφ.integrable.norm.const_mul
    (C * ∑ a ∈ A, s ^ (a / K.order) * lam ^ (γ - a)))
    ((hΛ.meas s hs.1).mul hφ.meas).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  by_cases hy : K.scaleDist y x₀ ≤ lam
  · exact mul_le_mul_of_nonneg_right (hΛ.abs_le hs hy) (abs_nonneg _)
  · rw [hφ.supp y (not_le.1 hy)]; simp

theorem LocalBall.integrable_mul_apply [SFinite μ] (hK : K.IsSymmetric)
    {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalBall Λ x₀ γ A C lam)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) {φ : E → ℝ}  (hφ : K.IsSupported φ x₀ lam)
    {h : ℝ} (hh : 0 < h) : Integrable (fun z => Λ s z * K.apply h φ z) μ :=
  K.integrable_mul_apply hK (hΛ.integrable_prod hs hφ hh)

theorem LocalBall.integral_apply_mul [SFinite μ] (hK : K.IsSymmetric)
    {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalBall Λ x₀ γ A C lam)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) {φ : E → ℝ}  (hφ : K.IsSupported φ x₀ lam)
    {h : ℝ} (hh : 0 < h) :
    ∫ y, Λ (s + h) y * φ y ∂μ = ∫ z, Λ s z * K.apply h φ z ∂μ := by
  have : ∀ y, Λ (s + h) y = K.apply h (Λ s) y := fun y => by
    rw [add_comm]; exact (K.apply_eq hΛ.mem hh hs.1 y).symm
  simp_rw [this]
  exact K.integral_mul_apply_eq hK (hΛ.integrable_prod hs hφ hh)

end RegularityStructures.RegularisingSemigroup

end
