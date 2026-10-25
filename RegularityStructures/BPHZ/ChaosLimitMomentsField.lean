/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsCylinder

/-!
# Uniform polynomial moments of a white-noise field

Let `ψ` be a random field such that every value `ψ(·, y)` is almost surely `W h_y` with `h_y ∈ L²`,
and `E ψ(y)² ≤ V` for all `y`. Then all moments of `ψ(y)` are bounded uniformly in `y`
(`exists_integral_field_pow_le`), and so are the moments of `Q(ψ(y))` for a polynomial `Q`
(`exists_integral_polyField_sq_mul_sq_le`).
-/

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A polynomial is bounded by a multiple of `1 + t^(2 * degree)`. -/
theorem exists_abs_eval_le_mul_one_add_pow (Q : Polynomial ℝ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t : ℝ, |Q.eval t| ≤ S * (1 + t ^ (2 * Q.natDegree)) := by
  refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|,
    Finset.sum_nonneg fun i _ => abs_nonneg _, fun t => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hi' : i ≤ 2 * Q.natDegree := by
    have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    omega
  have hev : |t| ^ (2 * Q.natDegree) = t ^ (2 * Q.natDegree) := by
    rw [pow_mul, pow_mul, sq_abs]
  rcases le_total |t| 1 with h | h
  · have := pow_le_one₀ (abs_nonneg t) h (n := i)
    have h2 : 0 ≤ t ^ (2 * Q.natDegree) := by rw [pow_mul]; positivity
    linarith
  · have := pow_le_pow_right₀ h hi'
    rw [hev] at this
    linarith

private lemma add_one_pow_four_le (s : ℝ) : (1 + s) ^ 4 ≤ 8 * (1 + s ^ 4) := by
  nlinarith [sq_nonneg (s + 1), sq_nonneg (s - 1), sq_nonneg (s ^ 2 - 1),
    sq_nonneg (s ^ 2 + 1), sq_nonneg s]

variable {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ψ : Ω → SpaceTime → ℝ}

/-- **Uniform moments of a white-noise field.** -/
theorem exists_integral_field_pow_le (hW : IsWhiteNoise P W)
    (hψW : ∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) {V : ℝ}
    (hV : ∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) (r : ℕ) (hr : 1 ≤ r) :
    ∃ M : ℝ, ∀ y, Integrable (fun ω => ψ ω y ^ (2 * r)) P ∧
      ∫ ω, ψ ω y ^ (2 * r) ∂P ≤ M := by
  obtain ⟨A, hA0, hA⟩ := exists_integral_pow_two_mul_le_of_isWhiteNoise.{u} 1 r hr
  refine ⟨A * (max V 0) ^ r, fun y => ?_⟩
  obtain ⟨h, hh, hae⟩ := hψW y
  have hvec := hW.2 1 (fun _ => h) (fun _ => hh)
  have hint := integrable_eval_pow_of_isCentredGaussianVector hvec
    (X 0 : MvPolynomial (Fin 1) ℝ) (2 * r)
  have hev : ∀ k : ℕ, (fun ω => eval (fun _ : Fin 1 => W h ω) (X 0 : MvPolynomial (Fin 1) ℝ) ^ k) =
      fun ω => W h ω ^ k := fun k => by simp
  refine ⟨?_, ?_⟩
  · simp only [hev] at hint
    exact hint.congr (by filter_upwards [hae] with ω hω; rw [hω])
  · have h1 := hA hW (fun _ : Fin 1 => h) (fun _ => hh) (X 0) (by simp)
    simp only [eval_X] at h1
    have e2 : ∀ k : ℕ, ∫ ω, ψ ω y ^ k ∂P = ∫ ω, W h ω ^ k ∂P := fun k =>
      integral_congr_ae (by filter_upwards [hae] with ω hω; rw [hω])
    rw [e2]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA0)
    rw [← e2]
    exact pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg _) ((hV y).trans (le_max_left _ _)) r

private lemma pow_le_one_add_pow_succ {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : u ^ k ≤ 1 + u ^ (k + 1) := by
  rcases le_total u 1 with h | h
  · have := pow_le_one₀ hu h (n := k)
    have : 0 ≤ u ^ (k + 1) := pow_nonneg hu _
    linarith
  · have := pow_le_pow_right₀ h (by omega : k ≤ k + 1)
    linarith

/-- **Uniform fourth moments of a polynomial of a white-noise field.** -/
theorem exists_integral_polyField_pow_four_le (hW : IsWhiteNoise P W)
    (hψW : ∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) {V : ℝ}
    (hV : ∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) (hψm : ∀ y, Measurable fun ω => ψ ω y)
    (Q : Polynomial ℝ) :
    ∃ M : ℝ, ∀ u, Integrable (fun ω => (Q.eval (ψ ω u)) ^ 4) P ∧
      ∫ ω, (Q.eval (ψ ω u)) ^ 4 ∂P ≤ M := by
  have := hW.isProbabilityMeasure
  obtain ⟨S, hS0, hS⟩ := exists_abs_eval_le_mul_one_add_pow Q
  obtain ⟨M, hM⟩ := exists_integral_field_pow_le hW hψW hV (4 * Q.natDegree + 1) (by omega)
  set d := Q.natDegree with hd
  have hpt : ∀ t : ℝ, (Q.eval t) ^ 4 ≤ 8 * S ^ 4 * (2 + t ^ (2 * (4 * d + 1))) := by
    intro t
    have h1 : (Q.eval t) ^ 4 ≤ (S * (1 + t ^ (2 * d))) ^ 4 := by
      rw [← Even.pow_abs (by decide : Even 4)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hS t) 4
    have h2 : (S * (1 + t ^ (2 * d))) ^ 4 ≤ S ^ 4 * (8 * (1 + (t ^ (2 * d)) ^ 4)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (add_one_pow_four_le _) (by positivity)
    have h3 : (t ^ (2 * d)) ^ 4 ≤ 1 + t ^ (2 * (4 * d + 1)) := by
      have := pow_le_one_add_pow_succ (sq_nonneg t) (4 * d)
      have e1 : (t ^ (2 * d)) ^ 4 = (t ^ 2) ^ (4 * d) := by
        rw [← pow_mul, ← pow_mul]; ring_nf
      have e2 : t ^ (2 * (4 * d + 1)) = (t ^ 2) ^ (4 * d + 1) := by rw [← pow_mul]
      rw [e1, e2]
      exact this
    have h4 : S ^ 4 * (8 * (1 + (t ^ (2 * d)) ^ 4)) ≤
        8 * S ^ 4 * (2 + t ^ (2 * (4 * d + 1))) := by
      have : 0 ≤ S ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h3 this]
    exact h1.trans (h2.trans h4)
  refine ⟨8 * S ^ 4 * (2 + M), fun u => ?_⟩
  have hmaj : Integrable (fun ω => 8 * S ^ 4 * (2 + ψ ω u ^ (2 * (4 * d + 1)))) P :=
    ((integrable_const (2 : ℝ)).add (hM u).1).const_mul _
  have hmeas : Measurable fun ω => (Q.eval (ψ ω u)) ^ 4 :=
    (Q.continuous.measurable.comp (hψm u)).pow_const 4
  refine ⟨Integrable.mono' hmaj hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_),
    ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt _
  · calc ∫ ω, (Q.eval (ψ ω u)) ^ 4 ∂P ≤ ∫ ω, 8 * S ^ 4 * (2 + ψ ω u ^ (2 * (4 * d + 1))) ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hmaj
          (Filter.Eventually.of_forall fun ω => hpt _)
      _ = 8 * S ^ 4 * ∫ ω, (2 + ψ ω u ^ (2 * (4 * d + 1))) ∂P := integral_const_mul _ _
      _ ≤ 8 * S ^ 4 * (2 + M) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [integral_add (integrable_const _) (hM u).1]
        have : (∫ ω, (2 : ℝ) ∂P) ≤ 2 := by simp
        linarith [(hM u).2]

/-- **Uniform moment of a product of two polynomials of a white-noise field**, evaluated at two
arbitrary points. -/
theorem exists_integral_polyField_sq_mul_sq_le (hW : IsWhiteNoise P W)
    (hψW : ∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) {V : ℝ}
    (hV : ∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) (hψm : ∀ y, Measurable fun ω => ψ ω y)
    (Q₁ Q₂ : Polynomial ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, Integrable (fun ω => (Q₁.eval (ψ ω u)) ^ 2 * (Q₂.eval (ψ ω v)) ^ 2) P ∧
      ∫ ω, (Q₁.eval (ψ ω u)) ^ 2 * (Q₂.eval (ψ ω v)) ^ 2 ∂P ≤ M := by
  obtain ⟨M₁, h₁⟩ := exists_integral_polyField_pow_four_le hW hψW hV hψm Q₁
  obtain ⟨M₂, h₂⟩ := exists_integral_polyField_pow_four_le hW hψW hV hψm Q₂
  refine ⟨max ((M₁ + M₂) / 2) 0, le_max_right _ _, fun u v => ?_⟩
  have hmaj : Integrable (fun ω => ((Q₁.eval (ψ ω u)) ^ 4 + (Q₂.eval (ψ ω v)) ^ 4) / 2) P :=
    ((h₁ u).1.add (h₂ v).1).div_const 2
  have hpt : ∀ a b : ℝ, a ^ 2 * b ^ 2 ≤ (a ^ 4 + b ^ 4) / 2 := fun a b => by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have hmeas : Measurable fun ω => (Q₁.eval (ψ ω u)) ^ 2 * (Q₂.eval (ψ ω v)) ^ 2 :=
    ((Q₁.continuous.measurable.comp (hψm u)).pow_const 2).mul
      ((Q₂.continuous.measurable.comp (hψm v)).pow_const 2)
  have hint : Integrable (fun ω => (Q₁.eval (ψ ω u)) ^ 2 * (Q₂.eval (ψ ω v)) ^ 2) P :=
    Integrable.mono' hmaj hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt _ _)
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ ω, ((Q₁.eval (ψ ω u)) ^ 4 + (Q₂.eval (ψ ω v)) ^ 4) / 2 ∂P :=
        integral_mono hint hmaj fun ω => hpt _ _
    _ = (∫ ω, (Q₁.eval (ψ ω u)) ^ 4 ∂P + ∫ ω, (Q₂.eval (ψ ω v)) ^ 4 ∂P) / 2 := by
        rw [integral_div, integral_add (h₁ u).1 (h₂ v).1]
    _ ≤ (M₁ + M₂) / 2 := by linarith [(h₁ u).2, (h₂ v).2]
    _ ≤ _ := le_max_left _ _

end RegularityStructures

end
