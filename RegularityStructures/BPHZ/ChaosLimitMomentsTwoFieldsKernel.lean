/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsTwoFields
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationSlab
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationInt
public import RegularityStructures.BPHZ.ChaosLimitMomentsFieldIntegral

/-!
# Moment equivalence for differences of tested kernel-chaos fields of two white-noise fields

Let `ψ`, `ψ'` be two continuous random fields, each almost surely a white-noise pairing at every
point with second moments bounded by `V`, `g` a measurable integrable test function supported in a
compact set `S`, `k(y, ·)` integrable kernels with `∫ |k(y, w)| dw ≤ L`, supported in `S` whenever
`g y ≠ 0`.  For polynomials `P₁, P₂, P₃` and `P₁', P₂', P₃'` with `deg P₁ + deg P₂ ≤ m`,
`deg P₃ ≤ m` (and likewise for the primed ones) put
`X = ∫ (chaosField ψ k P₁ P₂ P₃ - chaosField ψ' k P₁' P₂' P₃') g`.  Then `X^(2p)` is integrable
and `E X^(2p) ≤ A (E X²)^p` with `A = A(m, p)` (`integrable_and_integral_pow_two_mul_le_of_chaosIntegral_sub`).

The proof is that of `integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub` with the
kernel: the difference of the two sampled tested fields is a cylindrical polynomial of degree at
most `m` in the pairings of both fields (`exists_cylindrical_sub`).
-/

public section

open MvPolynomial MeasureTheory Filter Topology

namespace RegularityStructures

universe u

/-- The unsampled tested field times a test function supported in a compact set, with a kernel
supported there, is integrable pathwise. -/
theorem integrable_chaosField_mul_of_supported {Ω : Type*} [MeasurableSpace Ω]
    {ψ : Ω → SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ} {g : SpaceTime → ℝ} {L : ℝ}
    {S : Set SpaceTime} (hψc : ∀ ω, Continuous (ψ ω))
    (hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2) (hSc : IsCompact S)
    (hgm : Measurable g) (hgi : Integrable g) (hgS : ∀ y, g y ≠ 0 → y ∈ S)
    (hkm : Measurable (Function.uncurry k)) (hki : ∀ y, Integrable (k y))
    (hL : ∀ y, ∫ w, |k y w| ≤ L) (hkS : ∀ y, g y ≠ 0 → ∀ w, k y w ≠ 0 → w ∈ S)
    (P₁ P₂ P₃ : Polynomial ℝ) (ω : Ω) :
    Integrable (fun y => chaosField ψ k P₁ P₂ P₃ ω y * g y) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_eval_comp_le (hψc ω) hSc P₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_eval_comp_le (hψc ω) hSc P₂
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_abs_eval_comp_le (hψc ω) hSc P₃
  have hL0 : 0 ≤ L := (integral_nonneg fun w => abs_nonneg _).trans (hL 0)
  have hFm : Measurable (chaosField ψ k P₁ P₂ P₃ ω) :=
    (measurable_chaosField hψj hkm P₁ P₂ P₃).comp (measurable_const.prodMk measurable_id)
  refine Integrable.mono' (hgi.abs.mul_const (L * C₁ * C₂ + C₃)) (hFm.mul hgm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hy : g y = 0
  · simp [hy]
  · rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_add_le _ _).trans (add_le_add ?_ (hC₃ y (hgS y hy)))
    rw [abs_mul]
    exact mul_le_mul (abs_integral_kernel_mul_le (hki y) (hL y) hC₁0 (hkS y hy) hC₁)
      (hC₂ y (hgS y hy)) (abs_nonneg _) (mul_nonneg hL0 hC₁0)

/-- The tested unsampled field is the identity-sampled tested field. -/
theorem chaosIntegral_id_eq {Ω : Type*} (ψ : Ω → SpaceTime → ℝ) (k : SpaceTime → SpaceTime → ℝ)
    (P₁ P₂ P₃ : Polynomial ℝ) (g : SpaceTime → ℝ) (ω : Ω) :
    chaosIntegral ψ k P₁ P₂ P₃ g id ω = ∫ y, chaosField ψ k P₁ P₂ P₃ ω y * g y := by
  simp [chaosIntegral, chaosIntegrand, chaosInner, chaosField]

/-- **Moment equivalence for the difference of two tested kernel-chaos fields**, with integrability
of the `2p`-th power. -/
theorem integrable_and_integral_pow_two_mul_le_of_chaosIntegral_sub (m p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ψ ψ' : Ω → SpaceTime → ℝ}, (∀ ω, Continuous (ψ ω)) → (∀ ω, Continuous (ψ' ω)) →
      (∀ y, Measurable fun ω => ψ ω y) → (∀ y, Measurable fun ω => ψ' ω y) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ' ω y) =ᵐ[P] W h) →
      ∀ {V : ℝ}, (∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) → (∀ y, ∫ ω, ψ' ω y ^ 2 ∂P ≤ V) →
      ∀ {S : Set SpaceTime}, IsCompact S → S.Nonempty →
      ∀ {g : SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ} {L : ℝ},
        Measurable g → Integrable g → (∀ y, g y ≠ 0 → y ∈ S) →
        Measurable (Function.uncurry k) → (∀ y, Integrable (k y)) →
        (∀ y, ∫ w, |k y w| ≤ L) → (∀ y, g y ≠ 0 → ∀ w, k y w ≠ 0 → w ∈ S) →
      ∀ P₁ P₂ P₃ P₁' P₂' P₃' : Polynomial ℝ, P₁.natDegree + P₂.natDegree ≤ m → P₃.natDegree ≤ m →
        P₁'.natDegree + P₂'.natDegree ≤ m → P₃'.natDegree ≤ m →
        Integrable (fun ω => (∫ y, (chaosField ψ k P₁ P₂ P₃ ω y -
          chaosField ψ' k P₁' P₂' P₃' ω y) * g y) ^ (2 * p)) P ∧
        ∫ ω, (∫ y, (chaosField ψ k P₁ P₂ P₃ ω y - chaosField ψ' k P₁' P₂' P₃' ω y) *
            g y) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ y, (chaosField ψ k P₁ P₂ P₃ ω y -
            chaosField ψ' k P₁' P₂' P₃' ω y) * g y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integral_pow_two_mul_le_of_ae_tendsto_cylindricalPolynomial.{u} m p hp
  refine ⟨A, hA0, fun {Ω _ P W} hW {ψ ψ'} hψc hψc' hψm hψm' hψW hψW' {V} hV hV' {S} hSc hS0
    {g k L} hgm hgi hgS hkm hki hL hkS P₁ P₂ P₃ P₁' P₂' P₃' hd12 hd3 hd12' hd3' => ?_⟩
  have := hW.isProbabilityMeasure
  have hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ ω y)
      (fun ω => hψc ω) hψm).comp measurable_swap
  have hψj' : Measurable fun q : Ω × SpaceTime => ψ' q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ' ω y)
      (fun ω => hψc' ω) hψm').comp measurable_swap
  obtain ⟨π, hπm, hπf, hπS, hπt⟩ := exists_sampling_sequence hS0
  obtain ⟨B, hB⟩ := exists_integral_chaosIntegral_sq_le hW hψW hV hψm hψj hgm hgi hkm hki hL
    P₁ P₂ P₃
  obtain ⟨B', hB'⟩ := exists_integral_chaosIntegral_sq_le hW hψW' hV' hψm' hψj' hgm hgi hkm hki hL
    P₁' P₂' P₃'
  have hT : ∀ n x, π n x ∈ (hπf n).toFinset := fun n x => (hπf n).mem_toFinset.2 ⟨x, rfl⟩
  have hpoly := fun n => exists_mvPolynomial_chaosIntegral (ψ := ψ) hkm hki hL hgi P₁ P₂ P₃
    (hπm n) (hπf n).toFinset (hT n)
  have hpoly' := fun n => exists_mvPolynomial_chaosIntegral (ψ := ψ') hkm hki hL hgi P₁' P₂' P₃'
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
    (hfdeg n).trans (max_le ((hf₁ n).trans ((hqdeg n).trans (max_le hd12 hd3)))
      ((hf₂ n).trans ((hqdeg' n).trans (max_le hd12' hd3'))))
  set R : ℕ → Ω → ℝ := fun n ω => chaosIntegral ψ k P₁ P₂ P₃ g (π n) ω -
    chaosIntegral ψ' k P₁' P₂' P₃' g (π n) ω with hR
  have hRae : ∀ n, R n =ᵐ[P] fun ω => eval (fun i => W (hh n i) ω) (f n) := by
    intro n
    filter_upwards [hae₁ n, hae₂ n] with ω e1 e2
    rw [hfeval n ω, ← e1, ← e2, hR]
    simp only [hq n ω, hq' n ω]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop
      (𝓝 (chaosIntegral ψ k P₁ P₂ P₃ g id ω - chaosIntegral ψ' k P₁' P₂' P₃' g id ω)) :=
    Eventually.of_forall fun ω =>
      (tendsto_chaosIntegral hψc hSc hgm hgi hgS hkm hki hL hkS P₁ P₂ P₃ hπm hπS hπt ω).sub
        (tendsto_chaosIntegral hψc' hSc hgm hgi hgS hkm hki hL hkS P₁' P₂' P₃' hπm hπS hπt ω)
  have hBR : ∃ B'' : ℝ, ∀ n, ∫ ω, R n ω ^ 2 ∂P ≤ B'' := by
    refine ⟨2 * B + 2 * B', fun n => ?_⟩
    have i1 : Integrable (fun ω => (eval (fun i => W (h₁ n i) ω) (f₁ n)) ^ 2) P := by
      simpa using integrable_eval_pow_of_isCentredGaussianVector (hW.2 _ (h₁ n) (hm₁ n)) (f₁ n) 2
    have i2 : Integrable (fun ω => (eval (fun i => W (h₂ n i) ω) (f₂ n)) ^ 2) P := by
      simpa using integrable_eval_pow_of_isCentredGaussianVector (hW.2 _ (h₂ n) (hm₂ n)) (f₂ n) 2
    have e1 : ∫ ω, chaosIntegral ψ k P₁ P₂ P₃ g (π n) ω ^ 2 ∂P =
        ∫ ω, (eval (fun i => W (h₁ n i) ω) (f₁ n)) ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hae₁ n] with ω e1
      rw [hq n ω, ← e1]
    have e2 : ∫ ω, chaosIntegral ψ' k P₁' P₂' P₃' g (π n) ω ^ 2 ∂P =
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
  have hX : ∀ ω, chaosIntegral ψ k P₁ P₂ P₃ g id ω - chaosIntegral ψ' k P₁' P₂' P₃' g id ω =
      ∫ y, (chaosField ψ k P₁ P₂ P₃ ω y - chaosField ψ' k P₁' P₂' P₃' ω y) * g y := fun ω => by
    rw [chaosIntegral_id_eq, chaosIntegral_id_eq, ← integral_sub
      (integrable_chaosField_mul_of_supported hψc hψj hSc hgm hgi hgS hkm hki hL hkS P₁ P₂ P₃ ω)
      (integrable_chaosField_mul_of_supported hψc' hψj' hSc hgm hgi hgS hkm hki hL hkS P₁' P₂' P₃'
        ω)]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only [sub_mul])
  have h1 := hA hW R nn hh hmem f hdeg hRae hlim hBR
  have h2 := integrable_pow_two_mul_of_ae_tendsto_cylindricalPolynomial m p hp hW R nn hh hmem f
    hdeg hRae hlim hBR
  simp only [hX] at h1 h2
  exact ⟨h2, h1⟩

end RegularityStructures

end
