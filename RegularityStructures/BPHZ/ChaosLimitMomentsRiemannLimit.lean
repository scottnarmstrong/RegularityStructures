/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsRiemann

/-!
# Pathwise convergence of the sampled tested fields

If `ψ(ω, ·)` is continuous, `S` is compact, the test function `g` is supported in `S`, the kernel
`k(y, ·)` is supported in `S` whenever `g y ≠ 0` and `∫ |k(y, w)| dw ≤ L`, then for sampling maps
`πₙ` with values in `S` and `πₙ x → x` on `S`, the sampled tested fields `chaosIntegral … (πₙ) ω`
converge to `chaosIntegral … id ω` (dominated convergence, twice).
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

variable {Ω : Type*}

private lemma measurable_comp_field {ψ : Ω → SpaceTime → ℝ} (hψc : ∀ ω, Continuous (ψ ω))
    (Q : Polynomial ℝ) (ω : Ω) {π : SpaceTime → SpaceTime} (hπ : Measurable π) :
    Measurable fun w => Q.eval (ψ ω (π w)) :=
  (Q.continuous.comp (hψc ω)).measurable.comp hπ

/-- **Pathwise convergence of the sampled tested fields.** -/
theorem tendsto_chaosIntegral {ψ : Ω → SpaceTime → ℝ} (hψc : ∀ ω, Continuous (ψ ω))
    {S : Set SpaceTime} (hSc : IsCompact S) {g : SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ}
    {L : ℝ} (hgm : Measurable g) (hgi : Integrable g) (hgS : ∀ y, g y ≠ 0 → y ∈ S)
    (hkm : Measurable (Function.uncurry k)) (hki : ∀ y, Integrable (k y))
    (hL : ∀ y, ∫ w, |k y w| ≤ L) (hkS : ∀ y, g y ≠ 0 → ∀ w, k y w ≠ 0 → w ∈ S)
    (P₁ P₂ P₃ : Polynomial ℝ) {π : ℕ → SpaceTime → SpaceTime}
    (hπm : ∀ n, Measurable (π n)) (hπS : ∀ n x, π n x ∈ S)
    (hπt : ∀ x ∈ S, Tendsto (fun n => π n x) atTop (𝓝 x)) (ω : Ω) :
    Tendsto (fun n => chaosIntegral ψ k P₁ P₂ P₃ g (π n) ω) atTop
      (𝓝 (chaosIntegral ψ k P₁ P₂ P₃ g id ω)) := by
  have hcont : ∀ Q : Polynomial ℝ, Continuous fun u => Q.eval (ψ ω u) := fun Q =>
    Q.continuous.comp (hψc ω)
  have hbd : ∀ Q : Polynomial ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ S, |Q.eval (ψ ω u)| ≤ C := fun Q => by
    obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hcont Q).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun u hu =>
      (by simpa using hC u hu : |Q.eval (ψ ω u)| ≤ C).trans (le_max_left _ _)⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := hbd P₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := hbd P₂
  obtain ⟨C₃, hC₃0, hC₃⟩ := hbd P₃
  have hinner : ∀ y, g y ≠ 0 → Tendsto (fun n => chaosInner ψ k P₁ (π n) ω y) atTop
      (𝓝 (chaosInner ψ k P₁ id ω y)) := by
    intro y hy
    refine tendsto_integral_of_dominated_convergence (fun w => |k y w| * C₁) (fun n => ?_)
      ((hki y).abs.mul_const C₁) (fun n => Eventually.of_forall fun w => ?_)
      (Eventually.of_forall fun w => ?_)
    · exact ((hkm.comp (measurable_const.prodMk measurable_id)).mul
        (measurable_comp_field hψc P₁ ω (hπm n))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC₁ _ (hπS n w)) (abs_nonneg _)
    · by_cases hw : k y w = 0
      · simp [hw]
      · exact tendsto_const_nhds.mul
          ((hcont P₁).continuousAt.tendsto.comp (hπt w (hkS y hy w hw)))
  have hmeas_in : ∀ n, Measurable fun y => chaosInner ψ k P₁ (π n) ω y := fun n => by
    have hf : Measurable (fun q : SpaceTime × SpaceTime =>
        k q.1 q.2 * P₁.eval (ψ ω (π n q.2))) :=
      hkm.mul ((measurable_comp_field hψc P₁ ω (hπm n)).comp measurable_snd)
    exact hf.stronglyMeasurable.integral_prod_right'.measurable
  have hbin : ∀ n y, |chaosInner ψ k P₁ (π n) ω y| ≤ L * C₁ := fun n y => by
    have h1 : ‖chaosInner ψ k P₁ (π n) ω y‖ ≤ ∫ w, |k y w| * C₁ := by
      refine norm_integral_le_of_norm_le ((hki y).abs.mul_const C₁)
        (Eventually.of_forall fun w => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC₁ _ (hπS n w)) (abs_nonneg _)
    rw [integral_mul_const] at h1
    exact (Real.norm_eq_abs _ ▸ h1).trans (mul_le_mul_of_nonneg_right (hL y) hC₁0)
  refine tendsto_integral_of_dominated_convergence
    (fun y => |g y| * (L * C₁ * C₂ + C₃)) (fun n => ?_) (hgi.abs.mul_const _)
    (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · exact (((hmeas_in n).mul (measurable_comp_field hψc P₂ ω (hπm n))).add
      (measurable_comp_field hψc P₃ ω (hπm n))).mul hgm |>.aestronglyMeasurable
  · unfold chaosIntegrand
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_add_le _ _).trans (add_le_add ?_ (hC₃ _ (hπS n y)))
    rw [abs_mul]
    exact mul_le_mul (hbin n y) (hC₂ _ (hπS n y)) (abs_nonneg _)
      ((abs_nonneg _).trans (hbin n y))
  · by_cases hy : g y = 0
    · simp [chaosIntegrand, hy]
    · have hyS := hgS y hy
      exact (((hinner y hy).mul ((hcont P₂).continuousAt.tendsto.comp (hπt y hyS))).add
        ((hcont P₃).continuousAt.tendsto.comp (hπt y hyS))).mul_const (g y)

end RegularityStructures

end
