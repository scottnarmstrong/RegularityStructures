/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationSecond
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationL2
public import RegularityStructures.BPHZ.ChaosLimitMomentsCauchySchwarz

/-!
# Weighted Cauchy-Schwarz for slab-supported test functions

`slabSecondMoment_chaosField`: for the unsampled tested field `chaosField`, a continuous random
field `ψ` and kernels `k(y, ·)` supported in a compact set uniformly for `y` in a time slab, the
bound `E (∫ h F)² ≤ (∫ |h|)² M` holds for every measurable integrable `h` supported in a time slab
(the hypothesis `SlabSecondMoment` of the truncation argument). The pathwise boundedness of the
field on the slab, which is needed to apply `integral_sq_integral_mul_le`, comes from the
continuity of `ψ(ω, ·)` on compact sets.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ψ : Ω → SpaceTime → ℝ}
  {k : SpaceTime → SpaceTime → ℝ}

omit [MeasurableSpace Ω] in
/-- On a time slab the unsampled tested field is bounded, pathwise. -/
theorem exists_abs_chaosField_le (hψc : ∀ ω, Continuous (ψ ω)) {L : ℝ}
    (hki : ∀ y, Integrable (k y)) (hL : ∀ y, ∫ w, |k y w| ≤ L) (c R : ℝ)
    (hkS : ∃ S : Set SpaceTime, IsCompact S ∧
      ∀ y, |y.1 - c| ≤ R → ∀ w, k y w ≠ 0 → w ∈ S)
    (P₁ P₂ P₃ : Polynomial ℝ) (ω : Ω) :
    ∃ D : ℝ, ∀ y, |y.1 - c| ≤ R → |chaosField ψ k P₁ P₂ P₃ ω y| ≤ D := by
  obtain ⟨S, hSc, hSk⟩ := hkS
  have hK : IsCompact (Set.Icc (c - R) (c + R) ×ˢ (Set.univ : Set Torus3)) :=
    isCompact_Icc.prod isCompact_univ
  have hmem : ∀ y : SpaceTime, |y.1 - c| ≤ R →
      y ∈ Set.Icc (c - R) (c + R) ×ˢ (Set.univ : Set Torus3) := fun y hy =>
    ⟨⟨by linarith [(abs_le.1 hy).1], by linarith [(abs_le.1 hy).2]⟩, Set.mem_univ _⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_eval_comp_le (hψc ω) hSc P₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_eval_comp_le (hψc ω) hK P₂
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_abs_eval_comp_le (hψc ω) hK P₃
  have hL0 : 0 ≤ L := (integral_nonneg fun w => abs_nonneg _).trans (hL 0)
  refine ⟨L * C₁ * C₂ + C₃, fun y hy => ?_⟩
  refine (abs_add_le _ _).trans (add_le_add ?_ (hC₃ y (hmem y hy)))
  rw [abs_mul]
  exact mul_le_mul (abs_integral_kernel_mul_le (hki y) (hL y) hC₁0 (hSk y hy) hC₁)
    (hC₂ y (hmem y hy)) (abs_nonneg _) (by positivity)

/-- **Weighted Cauchy-Schwarz for the unsampled tested field and slab-supported weights.** -/
theorem slabSecondMoment_chaosField [IsProbabilityMeasure P]
    (hψc : ∀ ω, Continuous (ψ ω)) (hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2)
    (hkm : Measurable (Function.uncurry k)) (hki : ∀ y, Integrable (k y)) {L : ℝ}
    (hL : ∀ y, ∫ w, |k y w| ≤ L) (c : ℝ)
    (hkS : ∀ R : ℝ, ∃ S : Set SpaceTime, IsCompact S ∧
      ∀ y, |y.1 - c| ≤ R → ∀ w, k y w ≠ 0 → w ∈ S)
    (P₁ P₂ P₃ : Polynomial ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hHi : ∀ y, Integrable (fun ω => chaosField ψ k P₁ P₂ P₃ ω y ^ 2) P)
    (hM : ∀ y, ∫ ω, chaosField ψ k P₁ P₂ P₃ ω y ^ 2 ∂P ≤ M) :
    SlabSecondMoment P (chaosField ψ k P₁ P₂ P₃) c M := by
  intro R h hhm hhi hhs
  have hHm := measurable_chaosField hψj hkm P₁ P₂ P₃
  have hHb : ∀ ω, Integrable (fun y => |h y| * chaosField ψ k P₁ P₂ P₃ ω y ^ 2) := fun ω => by
    obtain ⟨D, hD⟩ := exists_abs_chaosField_le hψc hki hL c R (hkS R) P₁ P₂ P₃ ω
    refine Integrable.mono' (hhi.abs.mul_const (D ^ 2)) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((continuous_abs.measurable.comp hhm).mul
        ((hHm.comp (measurable_const.prodMk measurable_id)).pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
      by_cases hy : h y = 0
      · simp [hy]
      · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := pow_le_pow_left₀ (abs_nonneg _) (hD y (hhs y hy)) 2
        rwa [sq_abs] at this
  exact integral_sq_integral_mul_le (P := P) (ν := volume) (k := h) hhm hhi
    (le_refl (∫ y, |h y|)) hM0 (H := chaosField ψ k P₁ P₂ P₃) hHm hHb hHi hM

end RegularityStructures

end
