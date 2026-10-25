/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsTwoFieldsKernel
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationLimit

/-!
# Moment equivalence for differences of tested kernel-chaos fields, test function without compact
# support

`integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation` is the version of
`integrable_and_integral_pow_two_mul_le_of_chaosIntegral_sub` for a measurable integrable test
function `g` that need not have compact support in time, with the same constant `A = A(m, p)`.
The kernel `k(y, ·)` must be supported in a compact set uniformly for `y` in each time slab.

The proof applies the compactly supported theorem to the time truncations of `g` and passes to the
limit with `integrable_and_integral_pow_two_mul_le_of_timeTruncation`; the weighted Cauchy-Schwarz
hypothesis `SlabSecondMoment` for the difference of the two fields is proved from the pathwise
boundedness of both fields on time slabs (`slabSecondMoment_chaosField_sub`).
-/

public section

open MeasureTheory

namespace RegularityStructures

universe u

section Slab

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ψ ψ' : Ω → SpaceTime → ℝ}
  {k : SpaceTime → SpaceTime → ℝ}

/-- **Weighted Cauchy-Schwarz on time slabs for the difference of two tested kernel-chaos
fields.** -/
theorem slabSecondMoment_chaosField_sub [IsProbabilityMeasure P]
    (hψc : ∀ ω, Continuous (ψ ω)) (hψc' : ∀ ω, Continuous (ψ' ω))
    (hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2)
    (hψj' : Measurable fun q : Ω × SpaceTime => ψ' q.1 q.2)
    (hkm : Measurable (Function.uncurry k)) (hki : ∀ y, Integrable (k y)) {L : ℝ}
    (hL : ∀ y, ∫ w, |k y w| ≤ L) (c : ℝ)
    (hkS : ∀ R : ℝ, ∃ S : Set SpaceTime, IsCompact S ∧
      ∀ y, |y.1 - c| ≤ R → ∀ w, k y w ≠ 0 → w ∈ S)
    (P₁ P₂ P₃ P₁' P₂' P₃' : Polynomial ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hHi : ∀ y, Integrable (fun ω => (chaosField ψ k P₁ P₂ P₃ ω y -
      chaosField ψ' k P₁' P₂' P₃' ω y) ^ 2) P)
    (hM : ∀ y, ∫ ω, (chaosField ψ k P₁ P₂ P₃ ω y -
      chaosField ψ' k P₁' P₂' P₃' ω y) ^ 2 ∂P ≤ M) :
    SlabSecondMoment P (fun ω y => chaosField ψ k P₁ P₂ P₃ ω y -
      chaosField ψ' k P₁' P₂' P₃' ω y) c M := by
  intro R h hhm hhi hhs
  have hHm : Measurable fun q : Ω × SpaceTime => chaosField ψ k P₁ P₂ P₃ q.1 q.2 -
      chaosField ψ' k P₁' P₂' P₃' q.1 q.2 :=
    (measurable_chaosField hψj hkm P₁ P₂ P₃).sub (measurable_chaosField hψj' hkm P₁' P₂' P₃')
  have hHb : ∀ ω, Integrable (fun y => |h y| * (chaosField ψ k P₁ P₂ P₃ ω y -
      chaosField ψ' k P₁' P₂' P₃' ω y) ^ 2) := fun ω => by
    obtain ⟨D₁, hD₁⟩ := exists_abs_chaosField_le hψc hki hL c R (hkS R) P₁ P₂ P₃ ω
    obtain ⟨D₂, hD₂⟩ := exists_abs_chaosField_le hψc' hki hL c R (hkS R) P₁' P₂' P₃' ω
    refine Integrable.mono' (hhi.abs.mul_const ((D₁ + D₂) ^ 2)) ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · exact ((continuous_abs.measurable.comp hhm).mul
        ((hHm.comp (measurable_const.prodMk measurable_id)).pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
      by_cases hy : h y = 0
      · simp [hy]
      · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h1 : |chaosField ψ k P₁ P₂ P₃ ω y - chaosField ψ' k P₁' P₂' P₃' ω y| ≤ D₁ + D₂ :=
          (abs_sub _ _).trans (add_le_add (hD₁ y (hhs y hy)) (hD₂ y (hhs y hy)))
        have := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at this
  exact integral_sq_integral_mul_le (P := P) (ν := volume) (k := h) hhm hhi
    (le_refl (∫ y, |h y|)) hM0
    (H := fun ω y => chaosField ψ k P₁ P₂ P₃ ω y - chaosField ψ' k P₁' P₂' P₃' ω y) hHm hHb hHi hM

end Slab

/-- **Moment equivalence for the difference of two tested kernel-chaos fields, test function
without compact support**, with integrability of the `2p`-th power. -/
theorem integrable_and_integral_pow_two_mul_le_of_chaosField_sub_timeTruncation (m p : ℕ)
    (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ψ ψ' : Ω → SpaceTime → ℝ}, (∀ ω, Continuous (ψ ω)) → (∀ ω, Continuous (ψ' ω)) →
      (∀ y, Measurable fun ω => ψ ω y) → (∀ y, Measurable fun ω => ψ' ω y) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ' ω y) =ᵐ[P] W h) →
      ∀ {V : ℝ}, (∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) → (∀ y, ∫ ω, ψ' ω y ^ 2 ∂P ≤ V) →
      ∀ {g : SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ} {L : ℝ},
        Measurable g → Integrable g →
        Measurable (Function.uncurry k) → (∀ y, Integrable (k y)) →
        (∀ y, ∫ w, |k y w| ≤ L) →
        (∀ c R : ℝ, ∃ S : Set SpaceTime, IsCompact S ∧
          ∀ y, |y.1 - c| ≤ R → ∀ w, k y w ≠ 0 → w ∈ S) →
      ∀ P₁ P₂ P₃ P₁' P₂' P₃' : Polynomial ℝ, P₁.natDegree + P₂.natDegree ≤ m → P₃.natDegree ≤ m →
        P₁'.natDegree + P₂'.natDegree ≤ m → P₃'.natDegree ≤ m →
        Integrable (fun ω => (∫ y, (chaosField ψ k P₁ P₂ P₃ ω y -
          chaosField ψ' k P₁' P₂' P₃' ω y) * g y) ^ (2 * p)) P ∧
        ∫ ω, (∫ y, (chaosField ψ k P₁ P₂ P₃ ω y - chaosField ψ' k P₁' P₂' P₃' ω y) *
            g y) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ y, (chaosField ψ k P₁ P₂ P₃ ω y -
            chaosField ψ' k P₁' P₂' P₃' ω y) * g y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_chaosIntegral_sub.{u} m p hp
  refine ⟨A, hA0, fun {Ω _ P W} hW {ψ ψ'} hψc hψc' hψm hψm' hψW hψW' {V} hV hV' {g k L} hgm hgi
    hkm hki hL hkS P₁ P₂ P₃ P₁' P₂' P₃' hd12 hd3 hd12' hd3' => ?_⟩
  have := hW.isProbabilityMeasure
  have hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ ω y)
      (fun ω => hψc ω) hψm).comp measurable_swap
  have hψj' : Measurable fun q : Ω × SpaceTime => ψ' q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ' ω y)
      (fun ω => hψc' ω) hψm').comp measurable_swap
  have hkS0 : ∀ y : SpaceTime, ∃ S : Set SpaceTime, IsCompact S ∧ ∀ w, k y w ≠ 0 → w ∈ S :=
    fun y => by
      obtain ⟨S, hSc, hS⟩ := hkS y.1 0
      exact ⟨S, hSc, hS y (by simp)⟩
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_integral_chaosField_sq_le hW hψc hψW hV hψm hψj hkm hki hL
    hkS0 P₁ P₂ P₃
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_integral_chaosField_sq_le hW hψc' hψW' hV' hψm' hψj' hkm hki
    hL hkS0 P₁' P₂' P₃'
  set F : Ω → SpaceTime → ℝ := fun ω y => chaosField ψ k P₁ P₂ P₃ ω y -
    chaosField ψ' k P₁' P₂' P₃' ω y with hF
  have hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2 :=
    (measurable_chaosField hψj hkm P₁ P₂ P₃).sub (measurable_chaosField hψj' hkm P₁' P₂' P₃')
  have hF2 : ∀ y, Integrable (fun ω => F ω y ^ 2) P ∧ ∫ ω, F ω y ^ 2 ∂P ≤ 2 * M₁ + 2 * M₂ := by
    intro y
    have hmaj : Integrable (fun ω => 2 * chaosField ψ k P₁ P₂ P₃ ω y ^ 2 +
        2 * chaosField ψ' k P₁' P₂' P₃' ω y ^ 2) P :=
      ((hM₁ y).1.const_mul 2).add ((hM₂ y).1.const_mul 2)
    have hm : Measurable fun ω => F ω y ^ 2 :=
      (((measurable_chaosField hψj hkm P₁ P₂ P₃).comp (measurable_id.prodMk measurable_const)).sub
        ((measurable_chaosField hψj' hkm P₁' P₂' P₃').comp
          (measurable_id.prodMk measurable_const))).pow_const 2
    have hle : ∀ ω, F ω y ^ 2 ≤ 2 * chaosField ψ k P₁ P₂ P₃ ω y ^ 2 +
        2 * chaosField ψ' k P₁' P₂' P₃' ω y ^ 2 := fun ω => by
      simp only [hF]
      nlinarith [sq_nonneg (chaosField ψ k P₁ P₂ P₃ ω y + chaosField ψ' k P₁' P₂' P₃' ω y)]
    refine ⟨hmaj.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_), ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hle ω
    · calc ∫ ω, F ω y ^ 2 ∂P
          ≤ ∫ ω, 2 * chaosField ψ k P₁ P₂ P₃ ω y ^ 2 +
              2 * chaosField ψ' k P₁' P₂' P₃' ω y ^ 2 ∂P :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hmaj
              (Filter.Eventually.of_forall hle)
        _ = 2 * ∫ ω, chaosField ψ k P₁ P₂ P₃ ω y ^ 2 ∂P +
              2 * ∫ ω, chaosField ψ' k P₁' P₂' P₃' ω y ^ 2 ∂P := by
            rw [integral_add ((hM₁ y).1.const_mul 2) ((hM₂ y).1.const_mul 2), integral_const_mul,
              integral_const_mul]
        _ ≤ 2 * M₁ + 2 * M₂ := by linarith [(hM₁ y).2, (hM₂ y).2]
  have hCS := slabSecondMoment_chaosField_sub hψc hψc' hψj hψj' hkm hki hL 0 (fun R => hkS 0 R)
    P₁ P₂ P₃ P₁' P₂' P₃' (M := 2 * M₁ + 2 * M₂) (by positivity)
    (fun y => (hF2 y).1) (fun y => (hF2 y).2)
  have e : ∀ (h : SpaceTime → ℝ) (ω : Ω), ∫ y, h y * F ω y = ∫ y, (chaosField ψ k P₁ P₂ P₃ ω y -
      chaosField ψ' k P₁' P₂' P₃' ω y) * h y :=
    fun h ω => integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  have hmom : ∀ n : ℕ, Integrable (fun ω => (∫ y, timeTruncation 0 n g y * F ω y) ^ (2 * p)) P ∧
      ∫ ω, (∫ y, timeTruncation 0 n g y * F ω y) ^ (2 * p) ∂P ≤
        A * (∫ ω, (∫ y, timeTruncation 0 n g y * F ω y) ^ 2 ∂P) ^ p := by
    intro n
    obtain ⟨S, hSc, hSk⟩ := hkS 0 n
    have hKc : IsCompact (Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ (Set.univ : Set Torus3)) :=
      isCompact_Icc.prod isCompact_univ
    have hmem : ∀ y : SpaceTime, |y.1 - 0| ≤ n →
        y ∈ Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ (Set.univ : Set Torus3) := fun y hy =>
      ⟨⟨by linarith [(abs_le.1 hy).1], by linarith [(abs_le.1 hy).2]⟩, Set.mem_univ _⟩
    have hSc' : IsCompact (S ∪ Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ (Set.univ : Set Torus3)) :=
      hSc.union hKc
    have hS0 : (S ∪ Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ (Set.univ : Set Torus3)).Nonempty :=
      ⟨((0 : ℝ), (0 : Torus3)), Or.inr ⟨⟨by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
        by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩, Set.mem_univ _⟩⟩
    have hgS : ∀ y, timeTruncation 0 n g y ≠ 0 → y ∈ S ∪ Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ
        (Set.univ : Set Torus3) := fun y hy => Or.inr (hmem y (abs_le_of_timeTruncation_ne_zero hy))
    have hkS' : ∀ y, timeTruncation 0 n g y ≠ 0 → ∀ w, k y w ≠ 0 →
        w ∈ S ∪ Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ (Set.univ : Set Torus3) :=
      fun y hy w hw => Or.inl (hSk y (abs_le_of_timeTruncation_ne_zero hy) w hw)
    have hgm' := measurable_timeTruncation hgm 0 n
    have hgi' := integrable_timeTruncation hgi 0 n
    have h := hA hW hψc hψc' hψm hψm' hψW hψW' hV hV' hSc' hS0 hgm' hgi' hgS hkm hki hL hkS'
      P₁ P₂ P₃ P₁' P₂' P₃' hd12 hd3 hd12' hd3'
    simp only [e]
    exact h
  have key := integrable_and_integral_pow_two_mul_le_of_timeTruncation (p := p) (A := A) hFm hgm
    hgi hF2 hCS hmom
  simp only [e] at key
  exact key

end RegularityStructures

end
