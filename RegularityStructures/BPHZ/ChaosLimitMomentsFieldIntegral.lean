/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMoments
public import RegularityStructures.BPHZ.ChaosLimitMomentsRiemannLimit
public import RegularityStructures.BPHZ.ChaosLimitMomentsRiemannL2

/-!
# Moment equivalence for tested polynomial fields of a white-noise field

Let `ψ` be a continuous random field (for every `ω`) such that every value `ψ(·, y)` is almost
surely a white-noise pairing `W h_y` and `E ψ(y)² ≤ V`. Let `g` be a measurable integrable test
function supported in a compact set `S`, `k(y, ·)` integrable kernels with `∫ |k(y, w)| dw ≤ L` and
supported in `S` whenever `g y ≠ 0`, and `P₁, P₂, P₃` polynomials with `deg P₁ + deg P₂ ≤ m`,
`deg P₃ ≤ m`. Then
`X = ∫ (∫ k(y, w) P₁(ψ(w)) dw · P₂(ψ(y)) + P₃(ψ(y))) g(y) dy`
satisfies `E X^(2p) ≤ A (E X²)^p` with `A = A(m, p)` independent of everything else
(`integral_pow_two_mul_le_of_chaosIntegral`), and the same for `X = ∫ P(ψ(y)) g(y) dy`
(`integral_pow_two_mul_le_of_polyIntegral`).

The proof samples `ψ` along finitely-valued measurable maps `πₙ → id`: the sampled fields are
polynomials of degree `≤ m` in finitely many values of `ψ`, hence almost surely cylindrical
polynomials of `W`; they converge pathwise by continuity of `ψ(ω, ·)` and are bounded in `L²`
by crude fixed-noise moment bounds, so the almost sure limit theorem applies.
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

universe u

/-- **Moment equivalence for tested polynomial fields of a white-noise field.** -/
theorem integral_pow_two_mul_le_of_chaosIntegral (m p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ψ : Ω → SpaceTime → ℝ}, (∀ ω, Continuous (ψ ω)) → (∀ y, Measurable fun ω => ψ ω y) →
      (∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) →
      ∀ {V : ℝ}, (∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) →
      ∀ {S : Set SpaceTime}, IsCompact S → S.Nonempty →
      ∀ {g : SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ} {L : ℝ},
        Measurable g → Integrable g → (∀ y, g y ≠ 0 → y ∈ S) →
        Measurable (Function.uncurry k) → (∀ y, Integrable (k y)) →
        (∀ y, ∫ w, |k y w| ≤ L) → (∀ y, g y ≠ 0 → ∀ w, k y w ≠ 0 → w ∈ S) →
      ∀ P₁ P₂ P₃ : Polynomial ℝ, P₁.natDegree + P₂.natDegree ≤ m → P₃.natDegree ≤ m →
        ∫ ω, (∫ y, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) + P₃.eval (ψ ω y)) *
            g y) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ y, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) +
            P₃.eval (ψ ω y)) * g y) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integral_pow_two_mul_le_of_ae_tendsto_cylindricalPolynomial.{u} m p hp
  refine ⟨A, hA0, fun {Ω _ P W} hW {ψ} hψc hψm hψW {V} hV {S} hSc hS0 {g k L} hgm hgi hgS hkm hki
    hL hkS P₁ P₂ P₃ hd12 hd3 => ?_⟩
  have := hW.isProbabilityMeasure
  have hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun y ω => ψ ω y)
      (fun ω => hψc ω) hψm).comp measurable_swap
  obtain ⟨π, hπm, hπf, hπS, hπt⟩ := exists_sampling_sequence hS0
  obtain ⟨B, hB⟩ := exists_integral_chaosIntegral_sq_le hW hψW hV hψm hψj hgm hgi hkm hki hL
    P₁ P₂ P₃
  have hT : ∀ n x, π n x ∈ (hπf n).toFinset := fun n x => (hπf n).mem_toFinset.2 ⟨x, rfl⟩
  have hpoly := fun n => exists_mvPolynomial_chaosIntegral (ψ := ψ) hkm hki hL hgi P₁ P₂ P₃
    (hπm n) (hπf n).toFinset (hT n)
  choose q hqdeg hq using hpoly
  have hcyl := fun n => exists_cylindrical_eval_ae (P := P) (W := W) hψW
    (fun a : ↥(hπf n).toFinset => (a : SpaceTime)) (q n)
  choose nn hh hmem f hfdeg hae using hcyl
  refine hA hW (fun n ω => chaosIntegral ψ k P₁ P₂ P₃ g (π n) ω) nn hh hmem f
    (fun n => (hfdeg n).trans ((hqdeg n).trans (max_le hd12 hd3))) (fun n => ?_) ?_
    ⟨B, fun n => hB (hπm n) (hπf n)⟩
  · refine EventuallyEq.trans ?_ (hae n)
    exact Eventually.of_forall fun ω => hq n ω
  · refine Eventually.of_forall fun ω => ?_
    exact tendsto_chaosIntegral hψc hSc hgm hgi hgS hkm hki hL hkS P₁ P₂ P₃ hπm hπS hπt ω

end RegularityStructures

end
