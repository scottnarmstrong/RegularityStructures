/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsRiemannL2

/-!
# The unsampled tested field and its pointwise second moment

For a random field `ψ`, a kernel `k` and polynomials `P₁, P₂, P₃`, the field
`chaosField ψ k P₁ P₂ P₃ ω y = (∫ k(y, w) P₁(ψ(ω, w)) dw) P₂(ψ(ω, y)) + P₃(ψ(ω, y))`
is jointly measurable (`measurable_chaosField`) and, when `k(y, ·)` is supported in a compact set,
has second moment bounded uniformly in `y` (`exists_integral_chaosField_sq_le`). The proof is the
one of `exists_integral_chaosIntegral_sq_le` with the identity sampling map: weighted
Cauchy-Schwarz for the inner integral and uniform moment bounds for the polynomial values.
-/

@[expose] public section

namespace RegularityStructures

/-- The unsampled field
`(∫ k(y, w) P₁(ψ(ω, w)) dw) P₂(ψ(ω, y)) + P₃(ψ(ω, y))`. -/
noncomputable def chaosField {Ω : Type*} (ψ : Ω → SpaceTime → ℝ)
    (k : SpaceTime → SpaceTime → ℝ) (P₁ P₂ P₃ : Polynomial ℝ) (ω : Ω) (y : SpaceTime) : ℝ :=
  (∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) + P₃.eval (ψ ω y)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

universe u

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {ψ : Ω → SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ}

theorem measurable_chaosField (hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2)
    (hkm : Measurable (Function.uncurry k)) (P₁ P₂ P₃ : Polynomial ℝ) :
    Measurable fun q : Ω × SpaceTime => chaosField ψ k P₁ P₂ P₃ q.1 q.2 := by
  have hf : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      k r.1.2 r.2 * P₁.eval (ψ r.1.1 r.2)) :=
    (hkm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
      (P₁.continuous.measurable.comp (hψj.comp (measurable_fst.fst.prodMk measurable_snd)))
  have hin : Measurable (fun r : Ω × SpaceTime => ∫ w, k r.2 w * P₁.eval (ψ r.1 w)) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  exact (hin.mul (P₂.continuous.measurable.comp hψj)).add (P₃.continuous.measurable.comp hψj)

/-- A polynomial of a continuous function is bounded on a compact set. -/
theorem exists_abs_eval_comp_le {ψ' : SpaceTime → ℝ} (hψ' : Continuous ψ') {S : Set SpaceTime}
    (hS : IsCompact S) (Q : Polynomial ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ S, |Q.eval (ψ' u)| ≤ C := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (Q.continuous.comp hψ').continuousOn
  exact ⟨max C 0, le_max_right _ _, fun u hu =>
    (by simpa using hC u hu : |Q.eval (ψ' u)| ≤ C).trans (le_max_left _ _)⟩

/-- The inner integral of the field is bounded by `L C` when `P₁ ∘ ψ` is bounded by `C` on a
compact set carrying the support of `k(y, ·)`. -/
theorem abs_integral_kernel_mul_le {k' : SpaceTime → ℝ} {F' : SpaceTime → ℝ} {S : Set SpaceTime}
    {L C : ℝ} (hki : Integrable k') (hL : ∫ w, |k' w| ≤ L) (hC0 : 0 ≤ C)
    (hS : ∀ w, k' w ≠ 0 → w ∈ S) (hC : ∀ w ∈ S, |F' w| ≤ C) :
    |∫ w, k' w * F' w| ≤ L * C := by
  have h1 : ‖∫ w, k' w * F' w‖ ≤ ∫ w, |k' w| * C := by
    refine norm_integral_le_of_norm_le (hki.abs.mul_const C) (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hw : k' w = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_left (hC w (hS w hw)) (abs_nonneg _)
  rw [integral_mul_const] at h1
  exact (Real.norm_eq_abs _ ▸ h1).trans (mul_le_mul_of_nonneg_right hL hC0)

end Measurability

end RegularityStructures

end
