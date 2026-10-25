/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMoments
public import RegularityStructures.BPHZ.ChaosLimitMomentsFieldIntegral

/-!
# Integrability of the moments of tested polynomial fields

The moment equivalence theorems `integral_pow_two_mul_le_of_chaosIntegral` do not record that
`X^(2p)` is integrable (for a non-integrable function the Bochner integral is `0`). Here we show
it: an almost sure limit `X` of cylindrical polynomials of degree at most `m` with bounded second
moments has `X^(2p)` integrable (`integrable_pow_two_mul_of_ae_tendsto_cylindricalPolynomial`),
by Fatou's lemma with the uniform bound `E Rₖ^(2p) ≤ A (E Rₖ²)^p`; the tested polynomial fields
with a compactly supported test function are such limits
(`integrable_pow_two_mul_of_chaosIntegral`, with the same hypotheses as
`integral_pow_two_mul_le_of_chaosIntegral`).
-/

public section

open MvPolynomial MeasureTheory Filter Topology

namespace RegularityStructures

universe u

/-- **Integrability of the `2p`-th moment of an almost sure limit of cylindrical polynomials.** -/
theorem integrable_pow_two_mul_of_ae_tendsto_cylindricalPolynomial (m p : ℕ) (hp : 1 ≤ p)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {X : Ω → ℝ} (R : ℕ → Ω → ℝ) (n : ℕ → ℕ)
    (h : ∀ k, Fin (n k) → SpaceTime → ℝ) (hh : ∀ k i, MemLp (h k i) 2)
    (f : ∀ k, MvPolynomial (Fin (n k)) ℝ) (hf : ∀ k, (f k).totalDegree ≤ m)
    (hRae : ∀ k, R k =ᵐ[P] fun ω => eval (fun i => W (h k i) ω) (f k))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => R k ω) atTop (𝓝 (X ω)))
    (hB : ∃ B : ℝ, ∀ k, ∫ ω, R k ω ^ 2 ∂P ≤ B) :
    Integrable (fun ω => X ω ^ (2 * p)) P := by
  obtain ⟨A₂, hA₂0, hA₂⟩ := exists_integral_pow_two_mul_le_of_isWhiteNoise.{u} m p hp
  obtain ⟨B, hB⟩ := hB
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  set Fk : ∀ k, Ω → ℝ := fun k ω => eval (fun i => W (h k i) ω) (f k) with hFk
  have hFmeas : ∀ k, Measurable (Fk k) := fun k =>
    (f k).continuous_eval.measurable.comp (measurable_pi_iff.2 fun i => hW.1 _ (hh k i))
  have hFint : ∀ k j, Integrable (fun ω => (Fk k ω) ^ j) P := fun k j =>
    integrable_eval_pow_of_isCentredGaussianVector (hW.2 _ (h k) (hh k)) (f k) j
  have hall : ∀ᵐ ω ∂P, ∀ k, R k ω = Fk k ω := ae_all_iff.2 hRae
  have hlimF : ∀ᵐ ω ∂P, Tendsto (fun k => Fk k ω) atTop (𝓝 (X ω)) := by
    filter_upwards [hall, hlim] with ω h1 h2
    simpa only [h1] using h2
  have hB2 : ∀ k, ∫ ω, Fk k ω ^ 2 ∂P ≤ B := fun k => by
    have := integral_congr_ae (μ := P) (f := fun ω => R k ω ^ 2) (g := fun ω => Fk k ω ^ 2)
      (by filter_upwards [hRae k] with ω hω; rw [hω])
    rw [← this]
    exact hB k
  have hp2 : ∀ k, ∫ ω, Fk k ω ^ (2 * p) ∂P ≤ A₂ * B ^ p := fun k =>
    (hA₂ hW (h k) (hh k) (f k) (hf k)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg (Fk k ω)) (hB2 k) p) hA₂0)
  exact (integrable_and_integral_le_of_ae_tendsto (μ := P)
    (G := fun k ω => Fk k ω ^ (2 * p)) (G' := fun ω => X ω ^ (2 * p)) (b := fun _ => A₂ * B ^ p)
    (B := A₂ * B ^ p) (fun k => (hFmeas k).pow_const _)
    (fun k ω => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) (fun k => hFint k _)
    (by
      filter_upwards [hlimF] with ω hω
      exact hω.pow (2 * p))
    hp2 tendsto_const_nhds).1

/-- **Integrability of the `2p`-th moment of a tested polynomial field** (the hypotheses of
`integral_pow_two_mul_le_of_chaosIntegral`). -/
theorem integrable_pow_two_mul_of_chaosIntegral (m p : ℕ) (hp : 1 ≤ p) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ψ : Ω → SpaceTime → ℝ} (hψc : ∀ ω, Continuous (ψ ω)) (hψm : ∀ y, Measurable fun ω => ψ ω y)
    (hψW : ∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h)
    {V : ℝ} (hV : ∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) {S : Set SpaceTime} (hSc : IsCompact S)
    (hS0 : S.Nonempty) {g : SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ} {L : ℝ}
    (hgm : Measurable g) (hgi : Integrable g) (hgS : ∀ y, g y ≠ 0 → y ∈ S)
    (hkm : Measurable (Function.uncurry k)) (hki : ∀ y, Integrable (k y))
    (hL : ∀ y, ∫ w, |k y w| ≤ L) (hkS : ∀ y, g y ≠ 0 → ∀ w, k y w ≠ 0 → w ∈ S)
    (P₁ P₂ P₃ : Polynomial ℝ) (hd12 : P₁.natDegree + P₂.natDegree ≤ m) (hd3 : P₃.natDegree ≤ m) :
    Integrable (fun ω => (∫ y, ((∫ w, k y w * P₁.eval (ψ ω w)) * P₂.eval (ψ ω y) +
      P₃.eval (ψ ω y)) * g y) ^ (2 * p)) P := by
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
  refine integrable_pow_two_mul_of_ae_tendsto_cylindricalPolynomial m p hp hW
    (fun n ω => chaosIntegral ψ k P₁ P₂ P₃ g (π n) ω) nn hh hmem f
    (fun n => (hfdeg n).trans ((hqdeg n).trans (max_le hd12 hd3))) (fun n => ?_) ?_
    ⟨B, fun n => hB (hπm n) (hπf n)⟩
  · refine EventuallyEq.trans ?_ (hae n)
    exact Eventually.of_forall fun ω => hq n ω
  · refine Eventually.of_forall fun ω => ?_
    exact tendsto_chaosIntegral hψc hSc hgm hgi hgS hkm hki hL hkS P₁ P₂ P₃ hπm hπS hπt ω

end RegularityStructures

end
