/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianTailBound
public import RegularityStructures.Probability.GaussianGrowthIntegrability

/-!
# Polynomial control of the Gaussian Stein datum

The centred Gaussian density datum `(f - E f) φ` has both a finite Lebesgue integral and a
polynomial-times-Gaussian pointwise bound whenever `f` and its first derivative have the stated
polynomial growth.  This is the input that connects the explicit Stein construction to the tail
estimates in `GaussianTailBound.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

theorem gaussianStein_datum_polynomial_weight {f : ℝ → ℝ}
    (hcont_f : ContDiff ℝ 1 f)
    (hgrowth_f : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N) :
    let m : ℝ := ∫ y, f y ∂(gaussianReal 0 1)
    let q : ℝ → ℝ := fun x => (f x - m) * gaussianPDFReal 0 1 x
    Integrable q (volume : Measure ℝ) ∧
      (∫ x, q x) = 0 ∧
      ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
        ∀ x : ℝ, |q x| ≤ K * (1 + |x|) ^ N * rexp (-x ^ 2 / 2) := by
  dsimp
  rcases hgrowth_f with ⟨C, N, hC, hgrowth_f⟩
  let m : ℝ := ∫ y, f y ∂(gaussianReal 0 1)
  have hfbound : ∀ x : ℝ, |f x| ≤ C * (1 + ‖x‖) ^ N := by
    intro x
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hgrowth_f x)
  have hfint_gauss : Integrable f (gaussianReal 0 1) :=
    integrable_polynomially_bounded_gaussian hcont_f.continuous.measurable.aestronglyMeasurable
      ⟨C, N, hC, hfbound⟩
  have hfweight : Integrable
      (fun x => f x * gaussianPDFReal 0 1 x) (volume : Measure ℝ) :=
    integrable_gaussian_weight_of_integrable hfint_gauss
  have hpdfint : Integrable (gaussianPDFReal 0 1) (volume : Measure ℝ) :=
    integrable_gaussianPDFReal 0 1
  have hqint : Integrable
      (fun x => (f x - m) * gaussianPDFReal 0 1 x) (volume : Measure ℝ) := by
    have hsub : (fun x => (f x - m) * gaussianPDFReal 0 1 x) =
        (fun x => f x * gaussianPDFReal 0 1 x -
          m * gaussianPDFReal 0 1 x) := by
      funext x
      ring
    rw [hsub]
    exact hfweight.sub (hpdfint.const_mul m)
  have hzero : ∫ x, (f x - m) * gaussianPDFReal 0 1 x = 0 := by
    have hmean := integral_gaussianReal_eq_integral_smul (f := f) (μ := (0 : ℝ))
      (v := (1 : NNReal)) one_ne_zero
    have hpdfone : ∫ x, gaussianPDFReal 0 1 x = 1 :=
      integral_gaussianPDFReal_eq_one 0 one_ne_zero
    rw [show (fun x => (f x - m) * gaussianPDFReal 0 1 x) =
        (fun x => f x * gaussianPDFReal 0 1 x - m * gaussianPDFReal 0 1 x) by
          funext x; ring]
    rw [integral_sub hfweight (hpdfint.const_mul m), integral_const_mul, hpdfone]
    have hmean' : ∫ x, f x * gaussianPDFReal 0 1 x = m := by
      calc
        ∫ x, f x * gaussianPDFReal 0 1 x =
            ∫ x, gaussianPDFReal 0 1 x * f x := by
          congr 1
          funext x
          ring
        _ = m := by simpa [smul_eq_mul, m] using hmean.symm
    rw [hmean']
    ring
  have hqbound : ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
      ∀ x : ℝ, |(f x - m) * gaussianPDFReal 0 1 x| ≤
        K * (1 + |x|) ^ N * rexp (-x ^ 2 / 2) := by
    have hconst : 0 ≤ (√(2 * π))⁻¹ := by positivity
    refine ⟨(C + |m|) * (√(2 * π))⁻¹, N, ?_, ?_⟩
    · positivity
    intro x
    have hxnorm : ‖x‖ = |x| := Real.norm_eq_abs x
    have hpoly : 1 ≤ (1 + |x|) ^ N := by
      exact one_le_pow₀ (by linarith [abs_nonneg x])
    have hfm : |f x - m| ≤ (C + |m|) * (1 + |x|) ^ N := by
      have htriangle : |f x - m| ≤ |f x| + |m| := by
        calc
          |f x - m| ≤ |f x - 0| + |0 - m| := abs_sub_le (f x) 0 m
          _ = |f x| + |m| := by simp
      have hf' : |f x| ≤ C * (1 + |x|) ^ N := by
        simpa [hxnorm] using hfbound x
      calc
        |f x - m| ≤ |f x| + |m| := htriangle
        _ ≤ C * (1 + |x|) ^ N + |m| := by
          simpa [add_comm] using (add_le_add_right hf' |m|)
        _ ≤ (C + |m|) * (1 + |x|) ^ N := by
          have hm : |m| ≤ |m| * (1 + |x|) ^ N := by
            simpa [mul_comm] using mul_le_mul_of_nonneg_left hpoly (abs_nonneg m)
          calc
            C * (1 + |x|) ^ N + |m| ≤
                C * (1 + |x|) ^ N + |m| * (1 + |x|) ^ N :=
              by
                simpa [add_comm] using
                  (add_le_add_left hm (C * (1 + |x|) ^ N))
            _ = (C + |m|) * (1 + |x|) ^ N := by ring
    have hpdf : gaussianPDFReal 0 1 x =
        (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) := by
      simp [gaussianPDFReal_def]
    rw [abs_mul, hpdf, abs_mul, abs_of_nonneg hconst,
      abs_of_nonneg (Real.exp_pos _).le]
    have hfac : 0 ≤ (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) :=
      mul_nonneg hconst (Real.exp_pos _).le
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right hfm hfac)
  exact ⟨hqint, hzero, hqbound⟩

end RegularityStructures

end
