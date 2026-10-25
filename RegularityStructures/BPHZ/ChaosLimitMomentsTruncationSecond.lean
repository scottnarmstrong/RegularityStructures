/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationField

/-!
# Uniform pointwise second moment of the unsampled tested field

`exists_integral_chaosField_sq_le`: if `ψ(ω, ·)` is continuous, every `ψ(·, y)` is almost surely a
white-noise pairing with `E ψ(y)² ≤ V`, and `k(y, ·)` is integrable with `∫ |k(y, w)| dw ≤ L` and
supported in a compact set (depending on `y`), then `E chaosField(y)² ≤ M` for all `y`, with `M`
independent of `y`.
-/

public section

open MeasureTheory

namespace RegularityStructures

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ψ : Ω → SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ}

/-- **Uniform second moment of the unsampled field.** -/
theorem exists_integral_chaosField_sq_le (hW : IsWhiteNoise P W)
    (hψc : ∀ ω, Continuous (ψ ω))
    (hψW : ∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) {V : ℝ}
    (hV : ∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) (hψm : ∀ y, Measurable fun ω => ψ ω y)
    (hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2)
    (hkm : Measurable (Function.uncurry k)) (hki : ∀ y, Integrable (k y)) {L : ℝ}
    (hL : ∀ y, ∫ w, |k y w| ≤ L)
    (hkS : ∀ y, ∃ S : Set SpaceTime, IsCompact S ∧ ∀ w, k y w ≠ 0 → w ∈ S)
    (P₁ P₂ P₃ : Polynomial ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, Integrable (fun ω => chaosField ψ k P₁ P₂ P₃ ω y ^ 2) P ∧
      ∫ ω, chaosField ψ k P₁ P₂ P₃ ω y ^ 2 ∂P ≤ M := by
  have := hW.isProbabilityMeasure
  obtain ⟨M₁₂, hM₁₂0, hM₁₂⟩ := exists_integral_polyField_sq_mul_sq_le hW hψW hV hψm P₁ P₂
  obtain ⟨M₃, hM₃0, hM₃'⟩ :=
    exists_integral_polyField_sq_mul_sq_le hW hψW hV hψm P₃ (Polynomial.C 1)
  have hM₃ : ∀ v, Integrable (fun ω => (P₃.eval (ψ ω v)) ^ 2) P ∧
      ∫ ω, (P₃.eval (ψ ω v)) ^ 2 ∂P ≤ M₃ := fun v => by simpa using hM₃' v v
  have hL0 : 0 ≤ L := (integral_nonneg fun w => abs_nonneg _).trans (hL 0)
  refine ⟨2 * (L * (L * M₁₂) + M₃), by positivity, fun y => ?_⟩
  have hk_y : Measurable (k y) := hkm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨S, hSc, hSk⟩ := hkS y
  have hjoint : ∀ Q : Polynomial ℝ,
      Measurable (fun r : Ω × SpaceTime => Q.eval (ψ r.1 r.2)) := fun Q =>
    Q.continuous.measurable.comp hψj
  have hfix : ∀ (Q : Polynomial ℝ) (v : SpaceTime),
      Measurable (fun r : Ω × SpaceTime => Q.eval (ψ r.1 v)) := fun Q v =>
    Q.continuous.measurable.comp ((hψm v).comp measurable_fst)
  have hA : Integrable (fun ω => ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y)) ^ 2) P ∧
      ∫ ω, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y)) ^ 2 ∂P ≤ L * (L * M₁₂) := by
    have key := integral_sq_integral_mul_le (P := P) (ν := volume) (k := k y) hk_y (hki y)
      (hL y) hM₁₂0 (H := fun ω w => P₁.eval (ψ ω w) * P₂.eval (ψ ω y))
      ((hjoint P₁).mul (hfix P₂ y))
      (fun ω => by
        obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_eval_comp_le (hψc ω) hSc P₁
        refine Integrable.mono' ((hki y).abs.mul_const ((C₁ * |P₂.eval (ψ ω y)|) ^ 2))
          ((((continuous_abs.measurable.comp hk_y)).mul (((P₁.continuous.measurable.comp (hψc ω).measurable).mul_const _
            ).pow_const 2))).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
        by_cases hw : k y w = 0
        · simp [hw]
        · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have h1 : |P₁.eval (ψ ω w) * P₂.eval (ψ ω y)| ≤ C₁ * |P₂.eval (ψ ω y)| := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hC₁ w (hSk w hw)) (abs_nonneg _)
          have := pow_le_pow_left₀ (abs_nonneg _) h1 2
          rwa [sq_abs] at this)
      (fun w => by simpa only [mul_pow] using (hM₁₂ w y).1)
      (fun w => by simpa only [mul_pow] using (hM₁₂ w y).2)
    have e : ∀ ω, ∫ w, k y w * (P₁.eval (ψ ω w) * P₂.eval (ψ ω y)) =
        (∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) := fun ω => by
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)
    simp only [e] at key
    exact key
  have hHm : Measurable fun ω => chaosField ψ k P₁ P₂ P₃ ω y :=
    (measurable_chaosField hψj hkm P₁ P₂ P₃).comp (measurable_id.prodMk measurable_const)
  have hsq : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a - b)]
  have hHi : Integrable (fun ω => chaosField ψ k P₁ P₂ P₃ ω y ^ 2) P :=
    Integrable.mono' ((hA.1.const_mul 2).add ((hM₃ y).1.const_mul 2)) (hHm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsq _ _)
  refine ⟨hHi, ?_⟩
  calc ∫ ω, chaosField ψ k P₁ P₂ P₃ ω y ^ 2 ∂P
      ≤ ∫ ω, (2 * ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y)) ^ 2 +
          2 * (P₃.eval (ψ ω y)) ^ 2) ∂P :=
        integral_mono hHi ((hA.1.const_mul 2).add ((hM₃ y).1.const_mul 2)) fun ω => hsq _ _
    _ = 2 * ∫ ω, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y)) ^ 2 ∂P +
          2 * ∫ ω, (P₃.eval (ψ ω y)) ^ 2 ∂P := by
        rw [integral_add (hA.1.const_mul 2) ((hM₃ y).1.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * (L * (L * M₁₂) + M₃) := by
        have := hA.2
        have := (hM₃ y).2
        linarith

end RegularityStructures

end
