/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsAE

/-!
# Moment equivalence for almost sure limits of finite-chaos random variables

* `integral_pow_two_mul_le_of_ae_tendsto_cylindricalPolynomial`: if `Rₖ` are almost surely
  cylindrical polynomials of a white noise of degree at most `m`, `Rₖ → X` almost surely and
  `sup_k E Rₖ² < ∞`, then `E X^(2p) ≤ A * (E X²)^p`, with the constant `A = A(m, p)` of
  `integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial`.
-/

public section

open MvPolynomial MeasureTheory Filter Topology

namespace RegularityStructures

universe u

private lemma measurable_eval_white {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W) {n : ℕ} {h : Fin n → SpaceTime → ℝ}
    (hh : ∀ i, MemLp (h i) 2) (f : MvPolynomial (Fin n) ℝ) :
    Measurable fun ω => eval (fun i => W (h i) ω) f :=
  f.continuous_eval.measurable.comp (measurable_pi_iff.2 fun i => hW.1 _ (hh i))

private lemma pow_four_sub_le (a b : ℝ) : (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2),
    sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a * b)]

/-- **Moment equivalence for almost sure limits of cylindrical polynomials.** If `Rₖ` is almost
surely a polynomial of degree at most `m` in finitely many pairings of a white noise,
`Rₖ → X` almost surely and `E Rₖ²` is bounded, then `E X^(2p) ≤ A * (E X²)^p`, with the constant
`A` of `integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial`. -/
theorem integral_pow_two_mul_le_of_ae_tendsto_cylindricalPolynomial (m p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {X : Ω → ℝ} (R : ℕ → Ω → ℝ) (n : ℕ → ℕ) (h : ∀ k, Fin (n k) → SpaceTime → ℝ),
      (∀ k i, MemLp (h k i) 2) →
      ∀ f : ∀ k, MvPolynomial (Fin (n k)) ℝ, (∀ k, (f k).totalDegree ≤ m) →
      (∀ k, R k =ᵐ[P] fun ω => eval (fun i => W (h k i) ω) (f k)) →
      (∀ᵐ ω ∂P, Tendsto (fun k => R k ω) atTop (𝓝 (X ω))) →
      (∃ B : ℝ, ∀ k, ∫ ω, R k ω ^ 2 ∂P ≤ B) →
        ∫ ω, X ω ^ (2 * p) ∂P ≤ A * (∫ ω, X ω ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial.{u} m p hp
  obtain ⟨A₂, hA₂0, hA₂⟩ := exists_integral_pow_two_mul_le_of_isWhiteNoise.{u} m 2 (by norm_num)
  refine ⟨A, hA0, fun {Ω _ P W} hW {X} R n h hh f hf hRae hlim ⟨B, hB⟩ => ?_⟩
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  set Fk : ∀ k, Ω → ℝ := fun k ω => eval (fun i => W (h k i) ω) (f k) with hFk
  have hFmeas : ∀ k, Measurable (Fk k) := fun k => measurable_eval_white hW (hh k) (f k)
  have hFint : ∀ k j, Integrable (fun ω => (Fk k ω) ^ j) P := fun k j =>
    integrable_eval_pow_of_isCentredGaussianVector (hW.2 _ (h k) (hh k)) (f k) j
  have hall : ∀ᵐ ω ∂P, ∀ k, R k ω = Fk k ω := ae_all_iff.2 hRae
  have hlimF : ∀ᵐ ω ∂P, Tendsto (fun k => Fk k ω) atTop (𝓝 (X ω)) := by
    filter_upwards [hall, hlim] with ω h1 h2
    simpa only [h1] using h2
  have hXm : AEMeasurable X P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun k => (hFmeas k).aemeasurable) hlimF
  have hB2 : ∀ k, ∫ ω, Fk k ω ^ 2 ∂P ≤ B := fun k => by
    have := integral_congr_ae (μ := P) (f := fun ω => R k ω ^ 2) (g := fun ω => Fk k ω ^ 2)
      (by filter_upwards [hRae k] with ω hω; rw [hω])
    rw [← this]
    exact hB k
  have hB0 : 0 ≤ B := (integral_nonneg fun ω => sq_nonneg _).trans (hB2 0)
  have h4 : ∀ k, ∫ ω, Fk k ω ^ (2 * 2) ∂P ≤ A₂ * B ^ 2 := fun k =>
    (hA₂ hW (h k) (hh k) (f k) (hf k)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg (Fk k ω)) (hB2 k) 2) hA₂0)
  have hfat := integrable_and_integral_le_of_ae_tendsto (μ := P)
    (G := fun k ω => Fk k ω ^ (2 * 2)) (G' := fun ω => X ω ^ (2 * 2)) (b := fun _ => A₂ * B ^ 2)
    (B := A₂ * B ^ 2) (fun k => (hFmeas k).pow_const _)
    (fun k ω => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) (fun k => hFint k _)
    (by
      filter_upwards [hlimF] with ω hω
      exact (continuous_pow (2 * 2)).continuousAt.tendsto.comp hω)
    h4 tendsto_const_nhds
  have hX4 : Integrable (fun ω => X ω ^ 4) P := hfat.1
  have hXs : AEStronglyMeasurable X P := hXm.aestronglyMeasurable
  have hX2 : Integrable (fun ω => X ω ^ 2) P := by
    refine Integrable.mono' (hX4.add (integrable_const (1 : ℝ))) (hXs.pow 2)
      (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, norm_pow, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (X ω ^ 2 - 1), sq_nonneg (X ω)]
  have hZ4 : ∀ k, Integrable (fun ω => (Fk k ω - X ω) ^ 4) P := fun k => by
    refine Integrable.mono' (((hFint k 4).add hX4).const_mul 8) ((hFmeas k).aestronglyMeasurable.sub
      hXs |>.pow 4) (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, norm_pow, Real.norm_eq_abs]
    rw [pow_abs, abs_of_nonneg (by positivity)]
    exact pow_four_sub_le _ _
  have hlim2 : Tendsto (fun k => ∫ ω, (Fk k ω - X ω) ^ 2 ∂P) atTop (𝓝 0) := by
    refine tendsto_integral_sq_of_ae_tendsto_of_integral_pow_four_le
      (D := 8 * (A₂ * B ^ 2 + ∫ ω, X ω ^ 4 ∂P))
      (fun k => (hFmeas k).aestronglyMeasurable.sub hXs) hZ4 (fun k => ?_) ?_
    · calc ∫ ω, (Fk k ω - X ω) ^ 4 ∂P ≤ ∫ ω, 8 * (Fk k ω ^ 4 + X ω ^ 4) ∂P :=
          integral_mono (hZ4 k) (((hFint k 4).add hX4).const_mul 8) fun ω => pow_four_sub_le _ _
        _ = 8 * (∫ ω, Fk k ω ^ 4 ∂P + ∫ ω, X ω ^ 4 ∂P) := by
          rw [integral_const_mul, integral_add (hFint k 4) hX4]
        _ ≤ _ := by
          have := h4 k
          norm_num at this
          linarith
    · filter_upwards [hlimF] with ω hω
      simpa using hω.sub_const (X ω)
  exact hA hW hXs n h hh f hf hlim2

end RegularityStructures

end
