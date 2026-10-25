/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.WhiteNoiseChaosMomentsLinear
public import RegularityStructures.BPHZ.WhiteNoiseChaosMomentsLimit
public import RegularityStructures.Probability.GaussianVector

/-!
# Moment equivalence in finite white-noise chaos

For a white noise `W` and square-integrable test functions `h₁, …, hₙ`, a *cylindrical polynomial*
of degree at most `m` is `ω ↦ f (W h₁ ω, …, W hₙ ω)` with `f` a real polynomial of total degree at
most `m`.

* `exists_integral_pow_two_mul_le_of_isWhiteNoise`: all even moments of a cylindrical polynomial
  are bounded by a power of its variance, with a constant depending only on `m` and the exponent;
* `integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial`: the same bound, with the same
  constant, holds for `L²` limits of cylindrical polynomials of degree at most `m`
  (the finite-chaos case), by Fatou's lemma along an a.e. convergent subsequence.
-/

public section

open MvPolynomial MeasureTheory Filter Topology

namespace RegularityStructures

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A cylindrical polynomial of a white noise is measurable and has all moments. -/
private lemma measurable_cylindrical {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {n : ℕ} {h : Fin n → SpaceTime → ℝ} (hh : ∀ i, MemLp (h i) 2)
    (f : MvPolynomial (Fin n) ℝ) :
    Measurable fun ω => eval (fun i => W (h i) ω) f :=
  f.continuous_eval.measurable.comp (measurable_pi_iff.2 fun i => hW.1 _ (hh i))

/-- **Moment equivalence for cylindrical polynomials of a white noise.** The constant depends only
on the degree bound `m` and the exponent `p`. -/
theorem exists_integral_pow_two_mul_le_of_isWhiteNoise (m p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {n : ℕ} (h : Fin n → SpaceTime → ℝ), (∀ i, MemLp (h i) 2) →
      ∀ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ m →
        ∫ ω, (eval (fun i => W (h i) ω) f) ^ (2 * p) ∂P ≤
          A * (∫ ω, (eval (fun i => W (h i) ω) f) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := exists_integral_eval_pow_two_mul_le_of_isCentredGaussianVector.{u} m p hp
  exact ⟨A, hA0, fun {Ω _ P W} hW {n} h hh f hf => hA (hW.2 n h hh) f hf⟩

/-- **Closure of the moment equivalence under `L²` limits** (finite chaos of order `≤ m`).
If `F` is an `L²` limit of cylindrical polynomials of a white noise, all of degree at most `m`,
then `E[F^(2p)] ≤ A * E[F²]^p`, with the constant `A` of
`exists_integral_pow_two_mul_le_of_isWhiteNoise`. -/
theorem integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial (m p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {F : Ω → ℝ}, AEStronglyMeasurable F P →
      ∀ (n : ℕ → ℕ) (h : ∀ k, Fin (n k) → SpaceTime → ℝ), (∀ k i, MemLp (h k i) 2) →
      ∀ f : ∀ k, MvPolynomial (Fin (n k)) ℝ, (∀ k, (f k).totalDegree ≤ m) →
      Tendsto (fun k => ∫ ω, (eval (fun i => W (h k i) ω) (f k) - F ω) ^ 2 ∂P) atTop (𝓝 0) →
        ∫ ω, F ω ^ (2 * p) ∂P ≤ A * (∫ ω, F ω ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := exists_integral_pow_two_mul_le_of_isWhiteNoise.{u} m p hp
  refine ⟨A, hA0, fun {Ω _ P W} hW {F} hFm n h hh f hf hlim => ?_⟩
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  set Fk : ℕ → Ω → ℝ := fun k ω => eval (fun i => W (h k i) ω) (f k) with hFk
  have hint : ∀ k j, Integrable (fun ω => (Fk k ω) ^ j) P := fun k j =>
    integrable_eval_pow_of_isCentredGaussianVector (hW.2 _ (h k) (hh k)) (f k) j
  have hmemk : ∀ k, MemLp (Fk k) 2 P := fun k =>
    (memLp_two_iff_integrable_sq (measurable_cylindrical hW (hh k) (f k)).aestronglyMeasurable).2
      (hint k 2)
  by_cases hF2 : Integrable (fun ω => F ω ^ 2) P
  swap
  · rw [integral_undef hF2, zero_pow (by omega), mul_zero]
    by_cases hF2p : Integrable (fun ω => F ω ^ (2 * p)) P
    · exfalso
      refine hF2 (Integrable.mono' (hF2p.add (integrable_const (1 : ℝ)))
        (hFm.pow 2) (Eventually.of_forall fun ω => ?_))
      simp only [Pi.add_apply, norm_pow, Real.norm_eq_abs, sq_abs]
      have h3 : F ω ^ (2 * p) = (F ω ^ 2) ^ p := pow_mul _ _ _
      have h4 : 0 ≤ F ω ^ 2 := sq_nonneg _
      rcases le_total (F ω ^ 2) 1 with h1 | h1
      · have : 0 ≤ (F ω ^ 2) ^ p := pow_nonneg h4 _
        linarith
      · have := le_self_pow₀ h1 (by omega : p ≠ 0)
        linarith
    · rw [integral_undef hF2p]
  have hmemF : MemLp F 2 P := (memLp_two_iff_integrable_sq hFm).2 hF2
  obtain ⟨ns, hns, hae⟩ := exists_strictMono_ae_tendsto_of_tendsto_integral_sq_sub hmemk hmemF hlim
  have hS := (tendsto_integral_sq_of_tendsto_integral_sq_sub hmemk hmemF hlim).comp
    hns.tendsto_atTop
  have hb : Tendsto (fun j => A * (∫ ω, Fk (ns j) ω ^ 2 ∂P) ^ p) atTop
      (𝓝 (A * (∫ ω, F ω ^ 2 ∂P) ^ p)) :=
    (hS.pow p).const_mul A
  have hFmeas : ∀ k, Measurable (fun ω => (Fk (ns k) ω) ^ (2 * p)) := fun k =>
    (measurable_cylindrical hW (hh (ns k)) (f (ns k))).pow_const _
  refine (integrable_and_integral_le_of_ae_tendsto (G := fun j ω => (Fk (ns j) ω) ^ (2 * p))
    (G' := fun ω => F ω ^ (2 * p)) hFmeas (fun k ω => ?_) (fun k => hint (ns k) _) ?_
    (fun j => hA hW (h (ns j)) (hh (ns j)) (f (ns j)) (hf (ns j))) hb).2
  · rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  · filter_upwards [hae] with ω hω
    exact (continuous_pow (2 * p)).continuousAt.tendsto.comp hω


end RegularityStructures

end
