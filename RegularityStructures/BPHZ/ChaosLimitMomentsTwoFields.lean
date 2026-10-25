/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsFieldIntegral
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationInt
import Mathlib.Tactic

/-!
# Moment equivalence for differences of tested polynomial fields of two white-noise fields

Let `ψ`, `ψ'` be two continuous random fields, each almost surely a white-noise pairing at every
point, with second moments bounded by `V`, and let `g` be a measurable integrable test function
supported in a compact set.  For polynomials `Q`, `Q'` of degree at most `m` put
`X = ∫ Q(ψ) g - ∫ Q'(ψ') g`.  Then `X^(2p)` is integrable and
`E X^(2p) ≤ A (E X²)^p` with `A = A(m, p)` (`integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub`).

The proof is that of `integral_pow_two_mul_le_of_chaosIntegral` applied to both fields along the
same sampling sequence: the difference of two sampled tested fields is a cylindrical polynomial of
degree at most `m` in the pairings of both fields (`exists_cylindrical_sub`).
-/

public section

open MvPolynomial MeasureTheory Filter Topology

namespace RegularityStructures

universe u

/-- The difference of two cylindrical polynomials is a cylindrical polynomial. -/
theorem exists_cylindrical_sub {Ω : Type*} {W : (SpaceTime → ℝ) → Ω → ℝ} {n₁ n₂ : ℕ}
    {h₁ : Fin n₁ → SpaceTime → ℝ} {h₂ : Fin n₂ → SpaceTime → ℝ}
    (hh₁ : ∀ i, MemLp (h₁ i) 2) (hh₂ : ∀ i, MemLp (h₂ i) 2)
    (f₁ : MvPolynomial (Fin n₁) ℝ) (f₂ : MvPolynomial (Fin n₂) ℝ) :
    ∃ (n : ℕ) (h : Fin n → SpaceTime → ℝ), (∀ i, MemLp (h i) 2) ∧
      ∃ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ max f₁.totalDegree f₂.totalDegree ∧
        ∀ ω, eval (fun j => W (h j) ω) f =
          eval (fun i => W (h₁ i) ω) f₁ - eval (fun i => W (h₂ i) ω) f₂ := by
  set e : Fin n₁ ⊕ Fin n₂ ≃ Fin (n₁ + n₂) := finSumFinEquiv with he
  refine ⟨n₁ + n₂, fun j => Sum.elim h₁ h₂ (e.symm j), fun j => ?_,
    rename (e ∘ Sum.inl) f₁ - rename (e ∘ Sum.inr) f₂, ?_, fun ω => ?_⟩
  · rcases h : e.symm j with i | i
    · simpa [h] using hh₁ i
    · simpa [h] using hh₂ i
  · refine (totalDegree_sub _ _).trans (max_le_max ?_ ?_)
    · exact totalDegree_rename_le _ _
    · exact totalDegree_rename_le _ _
  · rw [map_sub, eval_rename, eval_rename]
    refine congrArg₂ (· - ·) (congrArg (fun x => eval x f₁) ?_)
      (congrArg (fun x => eval x f₂) ?_) <;> funext i <;> simp

/-- The tested polynomial field with the identity sampling map. -/
theorem chaosIntegral_zero_kernel_id {Ω : Type*} (ψ : Ω → SpaceTime → ℝ) (Q : Polynomial ℝ)
    (g : SpaceTime → ℝ) (ω : Ω) :
    chaosIntegral ψ (fun _ _ => 0) 0 0 Q g id ω = ∫ y, Q.eval (ψ ω y) * g y := by
  simp [chaosIntegral, chaosIntegrand, chaosInner]

/-- **Moment equivalence for the difference of two tested polynomial fields**, with integrability
of the `2p`-th power. -/
theorem integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub (m p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ψ ψ' : Ω → SpaceTime → ℝ}, (∀ ω, Continuous (ψ ω)) → (∀ ω, Continuous (ψ' ω)) →
      (∀ y, Measurable fun ω => ψ ω y) → (∀ y, Measurable fun ω => ψ' ω y) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ' ω y) =ᵐ[P] W h) →
      ∀ {V : ℝ}, (∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) → (∀ y, ∫ ω, ψ' ω y ^ 2 ∂P ≤ V) →
      ∀ {S : Set SpaceTime}, IsCompact S → S.Nonempty →
      ∀ {g : SpaceTime → ℝ}, Measurable g → Integrable g → (∀ y, g y ≠ 0 → y ∈ S) →
      ∀ Q Q' : Polynomial ℝ, Q.natDegree ≤ m → Q'.natDegree ≤ m →
        Integrable (fun ω => ((∫ y, Q.eval (ψ ω y) * g y) - ∫ y, Q'.eval (ψ' ω y) * g y) ^ (2 * p))
          P ∧
        ∫ ω, ((∫ y, Q.eval (ψ ω y) * g y) - ∫ y, Q'.eval (ψ' ω y) * g y) ^ (2 * p) ∂P ≤
          A * (∫ ω, ((∫ y, Q.eval (ψ ω y) * g y) - ∫ y, Q'.eval (ψ' ω y) * g y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integral_pow_two_mul_le_of_ae_tendsto_cylindricalPolynomial.{u} m p hp
  refine ⟨A, hA0, fun {Ω _ P W} hW {ψ ψ'} hψc hψc' hψm hψm' hψW hψW' {V} hV hV' {S} hSc hS0
    {g} hgm hgi hgS Q Q' hQ hQ' => ?_⟩
  have := hW.isProbabilityMeasure
  have hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ ω y)
      (fun ω => hψc ω) hψm).comp measurable_swap
  have hψj' : Measurable fun q : Ω × SpaceTime => ψ' q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ' ω y)
      (fun ω => hψc' ω) hψm').comp measurable_swap
  obtain ⟨π, hπm, hπf, hπS, hπt⟩ := exists_sampling_sequence hS0
  have hkm : Measurable (Function.uncurry fun (_ _ : SpaceTime) => (0 : ℝ)) := measurable_const
  have hki : ∀ y : SpaceTime, Integrable (fun _ : SpaceTime => (0 : ℝ)) := fun _ =>
    integrable_zero _ _ _
  have hL : ∀ y : SpaceTime, ∫ w : SpaceTime, |(fun (_ _ : SpaceTime) => (0 : ℝ)) y w| ≤ 0 :=
    fun y => by simp
  obtain ⟨B, hB⟩ := exists_integral_chaosIntegral_sq_le hW hψW hV hψm hψj hgm hgi hkm hki hL
    0 0 Q
  obtain ⟨B', hB'⟩ := exists_integral_chaosIntegral_sq_le hW hψW' hV' hψm' hψj' hgm hgi hkm hki hL
    0 0 Q'
  have hT : ∀ n x, π n x ∈ (hπf n).toFinset := fun n x => (hπf n).mem_toFinset.2 ⟨x, rfl⟩
  have hpoly := fun n => exists_mvPolynomial_chaosIntegral (ψ := ψ) hkm hki hL hgi 0 0 Q
    (hπm n) (hπf n).toFinset (hT n)
  have hpoly' := fun n => exists_mvPolynomial_chaosIntegral (ψ := ψ') hkm hki hL hgi 0 0 Q'
    (hπm n) (hπf n).toFinset (hT n)
  choose q hqdeg hq using hpoly
  choose q' hqdeg' hq' using hpoly'
  have hcyl := fun n => exists_cylindrical_eval_ae (P := P) (W := W) hψW
    (fun a : ↥(hπf n).toFinset => (a : SpaceTime)) (q n)
  have hcyl' := fun n => exists_cylindrical_eval_ae (P := P) (W := W) hψW'
    (fun a : ↥(hπf n).toFinset => (a : SpaceTime)) (q' n)
  choose n₁ h₁ hm₁ f₁ hf₁ hae₁ using hcyl
  choose n₂ h₂ hm₂ f₂ hf₂ hae₂ using hcyl'
  have hsub := fun n => exists_cylindrical_sub (W := W) (hm₁ n) (hm₂ n) (f₁ n) (f₂ n)
  choose nn hh hmem f hfdeg hfeval using hsub
  have hdeg : ∀ n, (f n).totalDegree ≤ m := fun n =>
    (hfdeg n).trans (max_le ((hf₁ n).trans ((hqdeg n).trans (by simpa using hQ)))
      ((hf₂ n).trans ((hqdeg' n).trans (by simpa using hQ'))))
  set R : ℕ → Ω → ℝ := fun n ω => chaosIntegral ψ (fun _ _ => 0) 0 0 Q g (π n) ω -
    chaosIntegral ψ' (fun _ _ => 0) 0 0 Q' g (π n) ω with hR
  have hRae : ∀ n, R n =ᵐ[P] fun ω => eval (fun i => W (hh n i) ω) (f n) := by
    intro n
    filter_upwards [hae₁ n, hae₂ n] with ω e1 e2
    rw [hfeval n ω, ← e1, ← e2, hR]
    simp only [hq n ω, hq' n ω]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop
      (𝓝 (chaosIntegral ψ (fun _ _ => 0) 0 0 Q g id ω -
        chaosIntegral ψ' (fun _ _ => 0) 0 0 Q' g id ω)) := by
    refine Eventually.of_forall fun ω => ?_
    exact (tendsto_chaosIntegral hψc hSc hgm hgi hgS hkm hki hL (fun y _ w hw => absurd rfl hw)
      0 0 Q hπm hπS hπt ω).sub
      (tendsto_chaosIntegral hψc' hSc hgm hgi hgS hkm hki hL (fun y _ w hw => absurd rfl hw)
      0 0 Q' hπm hπS hπt ω)
  have hBR : ∃ B'' : ℝ, ∀ n, ∫ ω, R n ω ^ 2 ∂P ≤ B'' := by
    refine ⟨2 * B + 2 * B', fun n => ?_⟩
    have hmeas1 : Measurable fun ω => eval (fun i => W (h₁ n i) ω) (f₁ n) := by
      exact (f₁ n).continuous_eval.measurable.comp
        (measurable_pi_iff.2 fun i => hW.1 _ (hm₁ n i))
    have hmeas2 : Measurable fun ω => eval (fun i => W (h₂ n i) ω) (f₂ n) :=
      (f₂ n).continuous_eval.measurable.comp (measurable_pi_iff.2 fun i => hW.1 _ (hm₂ n i))
    have i1 : Integrable (fun ω => (eval (fun i => W (h₁ n i) ω) (f₁ n)) ^ 2) P := by
      simpa using integrable_eval_pow_of_isCentredGaussianVector (hW.2 _ (h₁ n) (hm₁ n)) (f₁ n) 2
    have i2 : Integrable (fun ω => (eval (fun i => W (h₂ n i) ω) (f₂ n)) ^ 2) P := by
      simpa using integrable_eval_pow_of_isCentredGaussianVector (hW.2 _ (h₂ n) (hm₂ n)) (f₂ n) 2
    have e1 : ∫ ω, chaosIntegral ψ (fun _ _ => 0) 0 0 Q g (π n) ω ^ 2 ∂P =
        ∫ ω, (eval (fun i => W (h₁ n i) ω) (f₁ n)) ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hae₁ n] with ω e1
      rw [hq n ω, ← e1]
    have e2 : ∫ ω, chaosIntegral ψ' (fun _ _ => 0) 0 0 Q' g (π n) ω ^ 2 ∂P =
        ∫ ω, (eval (fun i => W (h₂ n i) ω) (f₂ n)) ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hae₂ n] with ω e2
      rw [hq' n ω, ← e2]
    have hb1 := hB (hπm n) (hπf n)
    have hb2 := hB' (hπm n) (hπf n)
    calc ∫ ω, R n ω ^ 2 ∂P
        = ∫ ω, (eval (fun i => W (h₁ n i) ω) (f₁ n) -
            eval (fun i => W (h₂ n i) ω) (f₂ n)) ^ 2 ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hae₁ n, hae₂ n] with ω e1 e2
          rw [hR]
          simp only [hq n ω, hq' n ω, e1, e2]
      _ ≤ ∫ ω, (2 * (eval (fun i => W (h₁ n i) ω) (f₁ n)) ^ 2 +
            2 * (eval (fun i => W (h₂ n i) ω) (f₂ n)) ^ 2) ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
            ((i1.const_mul 2).add (i2.const_mul 2)) (Eventually.of_forall fun ω => ?_)
          nlinarith [sq_nonneg (eval (fun i => W (h₁ n i) ω) (f₁ n) +
            eval (fun i => W (h₂ n i) ω) (f₂ n))]
      _ = 2 * ∫ ω, (eval (fun i => W (h₁ n i) ω) (f₁ n)) ^ 2 ∂P +
            2 * ∫ ω, (eval (fun i => W (h₂ n i) ω) (f₂ n)) ^ 2 ∂P := by
          rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * B + 2 * B' := by
          rw [← e1, ← e2]
          linarith
  have hX : ∀ ω, chaosIntegral ψ (fun _ _ => 0) 0 0 Q g id ω -
      chaosIntegral ψ' (fun _ _ => 0) 0 0 Q' g id ω =
      (∫ y, Q.eval (ψ ω y) * g y) - ∫ y, Q'.eval (ψ' ω y) * g y := fun ω => by
    rw [chaosIntegral_zero_kernel_id, chaosIntegral_zero_kernel_id]
  have h1 := hA hW R nn hh hmem f hdeg hRae hlim hBR
  have h2 := integrable_pow_two_mul_of_ae_tendsto_cylindricalPolynomial m p hp hW R nn hh hmem f
    hdeg hRae hlim hBR
  simp only [hX] at h1 h2
  exact ⟨h2, h1⟩

end RegularityStructures

end
