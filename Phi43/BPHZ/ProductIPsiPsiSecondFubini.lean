/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Second moment of a tested random field: Fubini

For `K ∈ L¹(μ)` and a jointly measurable field `F` with `E|F(a) F(a')| ≤ m(a, a')` and
`|K ⊗ K| m ∈ L¹(μ ⊗ μ)`,
`E[(∫ K F dμ)²] = ∫∫ K(a) K(a') E[F(a) F(a')] dμ dμ` (`integral_sq_integral_eq_integral_prod`).
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} {μ : Measure α}

/-- **Second moment of a tested field.** -/
theorem integral_sq_integral_eq_integral_prod [SFinite P] [SFinite μ] {K : α → ℝ}
    (hK : Measurable K) {F : Ω → α → ℝ} (hF : Measurable fun q : Ω × α => F q.1 q.2)
    (hFi : ∀ a a', Integrable (fun ω => F ω a * F ω a') P) {m : α → α → ℝ}
    (hm : ∀ a a', ∫ ω, |F ω a * F ω a'| ∂P ≤ m a a')
    (hint : Integrable (fun q : α × α => |K q.1 * K q.2| * m q.1 q.2) (μ.prod μ)) :
    ∫ ω, (∫ a, K a * F ω a ∂μ) ^ 2 ∂P =
      ∫ q : α × α, K q.1 * K q.2 * ∫ ω, F ω q.1 * F ω q.2 ∂P ∂(μ.prod μ) := by
  set f : Ω × (α × α) → ℝ := fun p => (K p.2.1 * K p.2.2) * (F p.1 p.2.1 * F p.1 p.2.2) with hf
  have hfm : Measurable f := by
    have h1 : Measurable (fun p : Ω × (α × α) => K p.2.1 * K p.2.2) :=
      (hK.comp (measurable_fst.comp measurable_snd)).mul (hK.comp (measurable_snd.comp measurable_snd))
    have h2 : Measurable (fun p : Ω × (α × α) => F p.1 p.2.1 * F p.1 p.2.2) :=
      (hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
        (hF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    exact h1.mul h2
  have hfi : Integrable f (P.prod (μ.prod μ)) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun q => ?_, ?_⟩
    · exact (hFi q.1 q.2).const_mul (K q.1 * K q.2)
    · refine Integrable.mono' hint ?_ (ae_of_all _ fun q => ?_)
      · exact hfm.aestronglyMeasurable.norm.prod_swap.integral_prod_right'
      · have e : ∫ ω, ‖f (ω, q)‖ ∂P = |K q.1 * K q.2| * ∫ ω, |F ω q.1 * F ω q.2| ∂P := by
          simp only [hf, norm_mul, Real.norm_eq_abs]
          rw [integral_const_mul]
          simp only [abs_mul]
        rw [e, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
          (integral_nonneg fun _ => abs_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hm q.1 q.2) (abs_nonneg _)
  have hsq : ∀ ω, (∫ a, K a * F ω a ∂μ) ^ 2 = ∫ q : α × α, f (ω, q) ∂(μ.prod μ) := by
    intro ω
    have h := integral_prod_mul (μ := μ) (ν := μ) (fun a => K a * F ω a) (fun a => K a * F ω a)
    rw [sq, ← h]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    simp only [hf]; ring
  simp_rw [hsq]
  rw [integral_integral_swap hfi]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [hf]
  rw [integral_const_mul]

end RegularityStructures

end
