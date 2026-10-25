/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncation
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Almost sure convergence of the truncated tested fields

Let `F : Ω → SpaceTime → ℝ` be jointly measurable with `E F(y)² ≤ M` for every `y`, on a
probability space, and let `g` be measurable and integrable on `ℝ × T³`. Then `(ω, y) ↦ g(y) F(ω, y)`
is integrable on `Ω × SpaceTime` (`integrable_prod_mul_of_second_moment`), so almost surely
`∫ g(y) F(ω, y) dy` converges absolutely, and the truncated integrals
`∫ timeTruncation c n g (y) F(ω, y) dy` converge to it
(`ae_tendsto_integral_timeTruncation_mul`).
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Ω → SpaceTime → ℝ}
  {g : SpaceTime → ℝ}

/-- The tested field `ω ↦ ∫ h(y) F(ω, y) dy` is measurable. -/
theorem measurable_integral_mul_field (hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2)
    {h : SpaceTime → ℝ} (hh : Measurable h) :
    Measurable fun ω => ∫ y, h y * F ω y := by
  have hf : Measurable fun q : Ω × SpaceTime => h q.2 * F q.1 q.2 :=
    (hh.comp measurable_snd).mul hFm
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

/-- A square integrable variable on a probability space is integrable. -/
private theorem integrable_of_integrable_sq [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) (h2 : Integrable (fun ω => f ω ^ 2) P) : Integrable f P := by
  refine Integrable.mono' (h2.add (integrable_const 1)) hf.aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f ω| - 1), sq_abs (f ω), abs_nonneg (f ω)]

/-- **Integrability of `g F` on `Ω × SpaceTime`.** -/
theorem integrable_prod_mul_of_second_moment [IsProbabilityMeasure P]
    (hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hgm : Measurable g)
    (hgi : Integrable g) {M : ℝ}
    (hF2 : ∀ y, Integrable (fun ω => F ω y ^ 2) P ∧ ∫ ω, F ω y ^ 2 ∂P ≤ M) :
    Integrable (fun q : Ω × SpaceTime => g q.2 * F q.1 q.2) (P.prod volume) := by
  have hm : Measurable fun q : Ω × SpaceTime => g q.2 * F q.1 q.2 :=
    (hgm.comp measurable_snd).mul hFm
  have hFy : ∀ y, Integrable (fun ω => F ω y) P := fun y =>
    integrable_of_integrable_sq (hFm.comp (measurable_id.prodMk measurable_const)) (hF2 y).1
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun y => (hFy y).const_mul (g y), ?_⟩
  refine Integrable.mono' (hgi.abs.mul_const (M + 1)) hm.norm.stronglyMeasurable.integral_prod_left.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have h1 : ∫ ω, ‖g y * F ω y‖ ∂P = |g y| * ∫ ω, |F ω y| ∂P := by
    simp only [norm_mul, Real.norm_eq_abs]
    exact integral_const_mul _ _
  have h2 : ∫ ω, |F ω y| ∂P ≤ M + 1 := by
    have hle : ∫ ω, |F ω y| ∂P ≤ ∫ ω, (F ω y ^ 2 + 1) ∂P :=
      integral_mono (hFy y).abs ((hF2 y).1.add (integrable_const 1)) fun ω => by
        nlinarith [sq_nonneg (|F ω y| - 1), sq_abs (F ω y), abs_nonneg (F ω y)]
    rw [integral_add (hF2 y).1 (integrable_const 1)] at hle
    simp only [integral_const, probReal_univ, one_smul] at hle
    linarith [(hF2 y).2]
  have h0 : 0 ≤ ∫ ω, |F ω y| ∂P := integral_nonneg fun ω => abs_nonneg _
  show ‖∫ ω, ‖g y * F ω y‖ ∂P‖ ≤ |g y| * (M + 1)
  rw [h1, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) h0)]
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/-- Almost surely `∫ truncᵣ(g) F(ω, ·)` converges to `∫ g F(ω, ·)`. -/
theorem ae_tendsto_integral_timeTruncation_mul [IsProbabilityMeasure P] (c : ℝ)
    (hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hgm : Measurable g)
    (hgi : Integrable g) {M : ℝ}
    (hF2 : ∀ y, Integrable (fun ω => F ω y ^ 2) P ∧ ∫ ω, F ω y ^ 2 ∂P ≤ M) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ y, timeTruncation c n g y * F ω y) atTop
      (𝓝 (∫ y, g y * F ω y)) := by
  filter_upwards [(integrable_prod_mul_of_second_moment hFm hgm hgi hF2).prod_right_ae] with ω hω
  exact tendsto_integral_timeTruncation_mul hgm (hFm.comp (measurable_const.prodMk measurable_id))
    hω

/-- Almost surely the truncated integrands are integrable. -/
theorem ae_integrable_timeTruncation_mul [IsProbabilityMeasure P] (c R : ℝ)
    (hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hgm : Measurable g)
    (hgi : Integrable g) {M : ℝ}
    (hF2 : ∀ y, Integrable (fun ω => F ω y ^ 2) P ∧ ∫ ω, F ω y ^ 2 ∂P ≤ M) :
    ∀ᵐ ω ∂P, Integrable (fun y => g y * F ω y) ∧
      Integrable (fun y => timeTruncation c R g y * F ω y) := by
  filter_upwards [(integrable_prod_mul_of_second_moment hFm hgm hgi hF2).prod_right_ae] with ω hω
  exact ⟨hω, integrable_timeTruncation_mul hgm (hFm.comp (measurable_const.prodMk measurable_id))
    hω⟩

end RegularityStructures

end
