/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationInt
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationLimit
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationSlab

/-!
# Moment equivalence with integrability, test function without compact support

`integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation` and
`integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation`: the equivalence of
moments for tested chaos fields and tested polynomial fields, for a test function that is not
compactly supported in time, together with the integrability of the `2p`-th power of the tested
field. The integrability is needed to turn the Bochner bound into a bound on `∫⁻ ‖·‖ₑ ^ q`.
-/

public section

open MeasureTheory

namespace RegularityStructures

universe u

/-- **Moment equivalence for tested chaos fields, test function without compact support, with
integrability of the `2p`-th power.** The proof applies the compactly supported case
`integral_pow_two_mul_le_of_chaosIntegral` to a truncation in time of the test function
(`timeTruncation`). -/
theorem integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation (m p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ψ : Ω → SpaceTime → ℝ}, (∀ ω, Continuous (ψ ω)) → (∀ y, Measurable fun ω => ψ ω y) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) →
      ∀ {V : ℝ}, (∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) →
      ∀ {g : SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ} {L : ℝ},
        Measurable g → Integrable g →
        Measurable (Function.uncurry k) → (∀ y, Integrable (k y)) →
        (∀ y, ∫ w, |k y w| ≤ L) →
        (∀ c R : ℝ, ∃ S : Set SpaceTime, IsCompact S ∧
          ∀ y, |y.1 - c| ≤ R → ∀ w, k y w ≠ 0 → w ∈ S) →
      ∀ P₁ P₂ P₃ : Polynomial ℝ, P₁.natDegree + P₂.natDegree ≤ m → P₃.natDegree ≤ m →
        Integrable (fun ω => (∫ y, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) +
            P₃.eval (ψ ω y)) * g y) ^ (2 * p)) P ∧
        ∫ ω, (∫ y, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) + P₃.eval (ψ ω y)) *
            g y) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ y, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) +
            P₃.eval (ψ ω y)) * g y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integral_pow_two_mul_le_of_chaosIntegral.{u} m p hp
  refine ⟨A, hA0, fun {Ω _ P W} hW {ψ} hψc hψm hψW {V} hV {g k L} hgm hgi hkm hki hL hkS
    P₁ P₂ P₃ hd12 hd3 => ?_⟩
  have := hW.isProbabilityMeasure
  have hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ ω y)
      (fun ω => hψc ω) hψm).comp measurable_swap
  obtain ⟨M, hM0, hM⟩ := exists_integral_chaosField_sq_le hW hψc hψW hV hψm hψj hkm hki hL
    (fun y => by
      obtain ⟨S, hSc, hS⟩ := hkS y.1 0
      exact ⟨S, hSc, hS y (by simp)⟩) P₁ P₂ P₃
  have hCS := slabSecondMoment_chaosField hψc hψj hkm hki hL 0 (fun R => hkS 0 R) P₁ P₂ P₃ hM0
    (fun y => (hM y).1) (fun y => (hM y).2)
  have e : ∀ (h : SpaceTime → ℝ) (ω : Ω), ∫ y, h y * chaosField ψ k P₁ P₂ P₃ ω y =
      ∫ y, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) + P₃.eval (ψ ω y)) * h y :=
    fun h ω => integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  have hmom : ∀ n : ℕ, Integrable (fun ω => (∫ y, timeTruncation 0 n g y *
        chaosField ψ k P₁ P₂ P₃ ω y) ^ (2 * p)) P ∧
      ∫ ω, (∫ y, timeTruncation 0 n g y * chaosField ψ k P₁ P₂ P₃ ω y) ^ (2 * p) ∂P ≤
        A * (∫ ω, (∫ y, timeTruncation 0 n g y *
          chaosField ψ k P₁ P₂ P₃ ω y) ^ 2 ∂P) ^ p := by
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
    have h1 := hA hW hψc hψm hψW hV hSc' hS0 hgm' hgi' hgS hkm hki hL hkS' P₁ P₂ P₃ hd12 hd3
    have h2 := integrable_pow_two_mul_of_chaosIntegral m p hp hW hψc hψm hψW hV hSc' hS0 hgm' hgi'
      hgS hkm hki hL hkS' P₁ P₂ P₃ hd12 hd3
    simp only [e]
    exact ⟨h2, h1⟩
  have key := integrable_and_integral_pow_two_mul_le_of_timeTruncation (p := p) (A := A)
    (measurable_chaosField hψj hkm P₁ P₂ P₃) hgm hgi (fun y => hM y) hCS hmom
  simp only [e] at key
  exact key
/-- **Moment equivalence for tested polynomial fields, test function without compact support, with
integrability of the `2p`-th power.** -/
theorem integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation (m p : ℕ)
    (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ψ : Ω → SpaceTime → ℝ}, (∀ ω, Continuous (ψ ω)) → (∀ y, Measurable fun ω => ψ ω y) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) →
      ∀ {V : ℝ}, (∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) →
      ∀ {g : SpaceTime → ℝ}, Measurable g → Integrable g →
      ∀ Q : Polynomial ℝ, Q.natDegree ≤ m →
        Integrable (fun ω => (∫ y, Q.eval (ψ ω y) * g y) ^ (2 * p)) P ∧
        ∫ ω, (∫ y, Q.eval (ψ ω y) * g y) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ y, Q.eval (ψ ω y) * g y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_chaosIntegral_timeTruncation.{u} m p hp
  refine ⟨A, hA0, fun {Ω _ P W} hW {ψ} hψc hψm hψW {V} hV {g} hgm hgi Q hQ => ?_⟩
  have h := hA hW hψc hψm hψW hV (k := fun _ _ => 0) (L := 0) hgm hgi
    (measurable_const) (fun _ => integrable_zero _ _ _) (fun y => by simp)
    (fun c R => ⟨∅, isCompact_empty, fun y _ w hw => absurd rfl hw⟩) 0 0 Q (by simp) hQ
  simpa using h

end RegularityStructures

end
