/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import RegularityStructures.BPHZ.ChaosLimitMomentsCauchySchwarz
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationField
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationLimit
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationL2
public import RegularityStructures.BPHZ.ChaosLimitMomentsTwoFields

/-!
# Moment equivalence for differences of tested fields, test function without compact support

`integrable_and_integral_pow_two_mul_le_of_continuousField`: for a jointly measurable random field
`F` with continuous paths and a uniform bound `E F(y)² ≤ M`, a measurable integrable test function
`g` and a moment equivalence `E X_n^(2p) ≤ A (E X_n²)^p` for the time truncations
`X_n = ∫ g_n F` (`g_n = timeTruncation 0 n g`) one gets the same for `X = ∫ g F`, with
integrability of `X^(2p)`.  The weighted Cauchy-Schwarz hypothesis `SlabSecondMoment` of the
truncation argument is supplied by the pathwise boundedness of `F` on time slabs
(`slabSecondMoment_of_continuousField`).

`integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub_timeTruncation` applies this to the
difference `Q(ψ) - Q'(ψ')` of two polynomial functionals of two white-noise fields, using the
compactly supported two-field theorem `integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub`
for the truncations.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Weighted Cauchy-Schwarz on time slabs for a field with continuous paths.** -/
theorem slabSecondMoment_of_continuousField [IsProbabilityMeasure P] {F : Ω → SpaceTime → ℝ}
    (hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hFc : ∀ ω, Continuous (F ω))
    {M : ℝ} (hM0 : 0 ≤ M) (hHi : ∀ y, Integrable (fun ω => F ω y ^ 2) P)
    (hM : ∀ y, ∫ ω, F ω y ^ 2 ∂P ≤ M) (c : ℝ) : SlabSecondMoment P F c M := by
  intro R h hhm hhi hhs
  have hK : IsCompact (Set.Icc (c - R) (c + R) ×ˢ (Set.univ : Set Torus3)) :=
    isCompact_Icc.prod isCompact_univ
  have hmem : ∀ y : SpaceTime, |y.1 - c| ≤ R →
      y ∈ Set.Icc (c - R) (c + R) ×ˢ (Set.univ : Set Torus3) := fun y hy =>
    ⟨⟨by linarith [(abs_le.1 hy).1], by linarith [(abs_le.1 hy).2]⟩, Set.mem_univ _⟩
  have hHb : ∀ ω, Integrable (fun y => |h y| * F ω y ^ 2) := fun ω => by
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hFc ω).continuousOn
    refine Integrable.mono' (hhi.abs.mul_const (D ^ 2)) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((continuous_abs.measurable.comp hhm).mul
        ((hFm.comp (measurable_const.prodMk measurable_id)).pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
      by_cases hy : h y = 0
      · simp [hy]
      · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h1 : |F ω y| ≤ D := by simpa using hD y (hmem y (hhs y hy))
        have := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs] at this
  exact integral_sq_integral_mul_le (P := P) (ν := volume) (k := h) hhm hhi
    (le_refl (∫ y, |h y|)) hM0 (H := F) hFm hHb hHi hM

/-- **Moment equivalence for a tested continuous field without compact support, from the time
truncations.** -/
theorem integrable_and_integral_pow_two_mul_le_of_continuousField [IsProbabilityMeasure P]
    {F : Ω → SpaceTime → ℝ} (hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2)
    (hFc : ∀ ω, Continuous (F ω)) {M A : ℝ} {p : ℕ}
    (hF2 : ∀ y, Integrable (fun ω => F ω y ^ 2) P ∧ ∫ ω, F ω y ^ 2 ∂P ≤ M)
    {g : SpaceTime → ℝ} (hgm : Measurable g) (hgi : Integrable g)
    (hmom : ∀ n : ℕ, Integrable (fun ω => (∫ y, timeTruncation 0 n g y * F ω y) ^ (2 * p)) P ∧
      ∫ ω, (∫ y, timeTruncation 0 n g y * F ω y) ^ (2 * p) ∂P ≤
        A * (∫ ω, (∫ y, timeTruncation 0 n g y * F ω y) ^ 2 ∂P) ^ p) :
    Integrable (fun ω => (∫ y, g y * F ω y) ^ (2 * p)) P ∧
      ∫ ω, (∫ y, g y * F ω y) ^ (2 * p) ∂P ≤ A * (∫ ω, (∫ y, g y * F ω y) ^ 2 ∂P) ^ p := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hF2 0).2
  exact integrable_and_integral_pow_two_mul_le_of_timeTruncation hFm hgm hgi hF2
    (slabSecondMoment_of_continuousField hFm hFc hM0 (fun y => (hF2 y).1) (fun y => (hF2 y).2) 0)
    hmom

/-- **Moment equivalence for the difference of two tested polynomial fields, test function without
compact support.**  The statement is for the tested difference `∫ (Q(ψ) - Q'(ψ')) g`. -/
theorem integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub_timeTruncation (m p : ℕ)
    (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ψ ψ' : Ω → SpaceTime → ℝ}, (∀ ω, Continuous (ψ ω)) → (∀ ω, Continuous (ψ' ω)) →
      (∀ y, Measurable fun ω => ψ ω y) → (∀ y, Measurable fun ω => ψ' ω y) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ' ω y) =ᵐ[P] W h) →
      ∀ {V : ℝ}, (∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) → (∀ y, ∫ ω, ψ' ω y ^ 2 ∂P ≤ V) →
      ∀ {g : SpaceTime → ℝ}, Measurable g → Integrable g →
      ∀ Q Q' : Polynomial ℝ, Q.natDegree ≤ m → Q'.natDegree ≤ m →
        Integrable (fun ω => (∫ y, (Q.eval (ψ ω y) - Q'.eval (ψ' ω y)) * g y) ^ (2 * p)) P ∧
        ∫ ω, (∫ y, (Q.eval (ψ ω y) - Q'.eval (ψ' ω y)) * g y) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ y, (Q.eval (ψ ω y) - Q'.eval (ψ' ω y)) * g y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub.{u} m p hp
  refine ⟨A, hA0, fun {Ω _ P W} hW {ψ ψ'} hψc hψc' hψm hψm' hψW hψW' {V} hV hV' {g} hgm hgi
    Q Q' hQ hQ' => ?_⟩
  have := hW.isProbabilityMeasure
  have hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ ω y)
      (fun ω => hψc ω) hψm).comp measurable_swap
  have hψj' : Measurable fun q : Ω × SpaceTime => ψ' q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ' ω y)
      (fun ω => hψc' ω) hψm').comp measurable_swap
  set F : Ω → SpaceTime → ℝ := fun ω y => Q.eval (ψ ω y) - Q'.eval (ψ' ω y) with hF
  have hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2 :=
    (Q.continuous.measurable.comp hψj).sub (Q'.continuous.measurable.comp hψj')
  have hFc : ∀ ω, Continuous (F ω) := fun ω =>
    (Q.continuous.comp (hψc ω)).sub (Q'.continuous.comp (hψc' ω))
  -- pointwise second moments
  obtain ⟨M₁, -, hM₁'⟩ := exists_integral_polyField_sq_mul_sq_le hW hψW hV hψm Q (Polynomial.C 1)
  obtain ⟨M₂, -, hM₂'⟩ := exists_integral_polyField_sq_mul_sq_le hW hψW' hV' hψm' Q' (Polynomial.C 1)
  have hM₁ : ∀ v, Integrable (fun ω => (Q.eval (ψ ω v)) ^ 2) P ∧
      ∫ ω, (Q.eval (ψ ω v)) ^ 2 ∂P ≤ M₁ := fun v => by simpa using hM₁' v v
  have hM₂ : ∀ v, Integrable (fun ω => (Q'.eval (ψ' ω v)) ^ 2) P ∧
      ∫ ω, (Q'.eval (ψ' ω v)) ^ 2 ∂P ≤ M₂ := fun v => by simpa using hM₂' v v
  have hF2 : ∀ y, Integrable (fun ω => F ω y ^ 2) P ∧
      ∫ ω, F ω y ^ 2 ∂P ≤ 2 * M₁ + 2 * M₂ := by
    intro y
    have hmaj : Integrable (fun ω => 2 * (Q.eval (ψ ω y)) ^ 2 + 2 * (Q'.eval (ψ' ω y)) ^ 2) P :=
      ((hM₁ y).1.const_mul 2).add ((hM₂ y).1.const_mul 2)
    have hm : Measurable fun ω => F ω y ^ 2 :=
      ((Q.continuous.measurable.comp (hψm y)).sub
        (Q'.continuous.measurable.comp (hψm' y))).pow_const 2
    have hle : ∀ ω, F ω y ^ 2 ≤ 2 * (Q.eval (ψ ω y)) ^ 2 + 2 * (Q'.eval (ψ' ω y)) ^ 2 :=
      fun ω => by
        simp only [hF]
        nlinarith [sq_nonneg (Q.eval (ψ ω y) + Q'.eval (ψ' ω y))]
    refine ⟨hmaj.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_), ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hle ω
    · calc ∫ ω, F ω y ^ 2 ∂P ≤ ∫ ω, 2 * (Q.eval (ψ ω y)) ^ 2 + 2 * (Q'.eval (ψ' ω y)) ^ 2 ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hmaj
            (Filter.Eventually.of_forall hle)
        _ = 2 * ∫ ω, (Q.eval (ψ ω y)) ^ 2 ∂P + 2 * ∫ ω, (Q'.eval (ψ' ω y)) ^ 2 ∂P := by
          rw [integral_add ((hM₁ y).1.const_mul 2) ((hM₂ y).1.const_mul 2), integral_const_mul,
            integral_const_mul]
        _ ≤ 2 * M₁ + 2 * M₂ := by linarith [(hM₁ y).2, (hM₂ y).2]
  -- truncated moments
  have hmom : ∀ n : ℕ, Integrable (fun ω => (∫ y, timeTruncation 0 n g y * F ω y) ^ (2 * p)) P ∧
      ∫ ω, (∫ y, timeTruncation 0 n g y * F ω y) ^ (2 * p) ∂P ≤
        A * (∫ ω, (∫ y, timeTruncation 0 n g y * F ω y) ^ 2 ∂P) ^ p := by
    intro n
    have hKc : IsCompact (Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ (Set.univ : Set Torus3)) :=
      isCompact_Icc.prod isCompact_univ
    have hS0 : (Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ (Set.univ : Set Torus3)).Nonempty :=
      ⟨((0 : ℝ), (0 : Torus3)), ⟨by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
        by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩, Set.mem_univ _⟩
    have hgS : ∀ y, timeTruncation 0 n g y ≠ 0 →
        y ∈ Set.Icc (0 - (n : ℝ)) (0 + n) ×ˢ (Set.univ : Set Torus3) := fun y hy =>
      have h := abs_le_of_timeTruncation_ne_zero hy
      ⟨⟨by linarith [(abs_le.1 h).1], by linarith [(abs_le.1 h).2]⟩, Set.mem_univ _⟩
    have hgm' := measurable_timeTruncation hgm 0 n
    have hgi' := integrable_timeTruncation hgi 0 n
    have h := hA hW hψc hψc' hψm hψm' hψW hψW' hV hV' hKc hS0 hgm' hgi' hgS Q Q' hQ hQ'
    -- the two tested integrals are integrable, so their difference is the tested difference
    have hint : ∀ (ψ₀ : SpaceTime → ℝ) (R : Polynomial ℝ), Continuous ψ₀ →
        Integrable (fun y => R.eval (ψ₀ y) * timeTruncation 0 n g y) := by
      intro ψ₀ R hc
      obtain ⟨D, hD0, hD⟩ := exists_abs_eval_comp_le hc hKc R
      refine Integrable.mono' (hgi'.abs.mul_const D) ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact ((R.continuous.comp hc).measurable.mul hgm').aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        by_cases hy : timeTruncation 0 n g y = 0
        · simp [hy]
        · exact mul_le_mul_of_nonneg_right (hD y (hgS y hy)) (abs_nonneg _) |>.trans_eq (by ring)
    have e : ∀ ω, ∫ y, timeTruncation 0 n g y * F ω y =
        (∫ y, Q.eval (ψ ω y) * timeTruncation 0 n g y) -
          ∫ y, Q'.eval (ψ' ω y) * timeTruncation 0 n g y := fun ω => by
      rw [← integral_sub (hint _ Q (hψc ω)) (hint _ Q' (hψc' ω))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hF]
      ring
    simp only [e]
    exact h
  have key := integrable_and_integral_pow_two_mul_le_of_continuousField hFm hFc hF2 hgm hgi hmom
  have e2 : ∀ ω, ∫ y, g y * F ω y = ∫ y, (Q.eval (ψ ω y) - Q'.eval (ψ' ω y)) * g y :=
    fun ω => integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  simp only [e2] at key
  exact key

end RegularityStructures

end
