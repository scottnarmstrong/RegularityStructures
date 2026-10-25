/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exchanging expectation and a kernel integral

Let `Y : Ω → α → ℝ` be a jointly a.e.-strongly measurable random field whose values have uniformly
bounded first absolute moments, `E|Y(w)| ≤ M` for every `w`, and let `K ∈ L¹(α)`. Then
`E[∫ K(w) Y(w) dw] = ∫ K(w) E[Y(w)] dw` (`integral_integral_mul_swap`). This is the Fubini step in
the identification of `C₂^ε` as a Gaussian expectation (the remark after Definition 2.5 of the
statement).
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} {μ : Measure α}

/-- The product `K(w) Y(ω, w)` is integrable on `Ω × α` when `K ∈ L¹` and `E|Y(w)| ≤ M`
uniformly. -/
theorem integrable_uncurry_mul_of_bound [SFinite P] [SFinite μ] {K : α → ℝ} (hK : Integrable K μ)
    {Y : Ω → α → ℝ} (hY : AEStronglyMeasurable (Function.uncurry Y) (P.prod μ))
    (hYi : ∀ w, Integrable (fun ω => Y ω w) P) {M : ℝ} (hM : ∀ w, ∫ ω, |Y ω w| ∂P ≤ M) :
    Integrable (Function.uncurry fun ω w => K w * Y ω w) (P.prod μ) := by
  have hFm : AEStronglyMeasurable (Function.uncurry fun ω w => K w * Y ω w) (P.prod μ) :=
    hK.aestronglyMeasurable.comp_snd.mul hY
  rw [integrable_prod_iff' hFm]
  refine ⟨ae_of_all _ fun w => (hYi w).const_mul (K w), ?_⟩
  refine Integrable.mono' (hK.norm.mul_const M) hFm.norm.prod_swap.integral_prod_right'
    (ae_of_all _ fun w => ?_)
  have hint : ∫ ω, ‖Function.uncurry (fun ω w => K w * Y ω w) (ω, w)‖ ∂P =
      |K w| * ∫ ω, |Y ω w| ∂P := by
    simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
    exact integral_const_mul _ _
  rw [hint, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _)), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM w) (abs_nonneg _)

/-- **Fubini for a kernel against a random field.** If `K ∈ L¹(μ)`, `Y` is jointly
a.e.-strongly measurable, each `Y(w)` is integrable and `E|Y(w)| ≤ M` for all `w`, then
`E[∫ K(w) Y(w) dμ(w)] = ∫ K(w) E[Y(w)] dμ(w)`. -/
theorem integral_integral_mul_swap [SFinite P] [SFinite μ] {K : α → ℝ} (hK : Integrable K μ)
    {Y : Ω → α → ℝ} (hY : AEStronglyMeasurable (Function.uncurry Y) (P.prod μ))
    (hYi : ∀ w, Integrable (fun ω => Y ω w) P) {M : ℝ} (hM : ∀ w, ∫ ω, |Y ω w| ∂P ≤ M) :
    ∫ ω, ∫ w, K w * Y ω w ∂μ ∂P = ∫ w, K w * ∫ ω, Y ω w ∂P ∂μ := by
  rw [integral_integral_swap (integrable_uncurry_mul_of_bound hK hY hYi hM)]
  congr 1
  funext w
  exact integral_const_mul _ _

end RegularityStructures

end
