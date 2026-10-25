/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCalculus

/-!
# Algebra for cylindrical divergence tests

These are the finite-dimensional identities used when a cylindrical derivative is itself used as
a Gaussian integration-by-parts test field.  In particular, a `C²` cylindrical test function has
`C¹` coordinate derivatives, and the derivative of `f ∂ᵢφ` is expanded explicitly.  The last
identity converts the spatial pairing of two cylindrical derivatives into the covariance matrix.
These are preparatory lemmas for the closability argument in [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem contDiff_coordinateDerivative {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiff ℝ 1 (fun x => coordinateDerivative f i x) := by
  have hfd : ContDiff ℝ 1
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (fderiv ℝ f p.1 : (Fin n → ℝ) → ℝ) p.2) := by
    exact hcont.contDiff_fderiv_apply (m := 1) (by norm_num)
  have hpair : ContDiff ℝ 1
      (fun x : Fin n → ℝ => (x, (Pi.single i 1 : Fin n → ℝ))) := by
    fun_prop
  have hcomp := hfd.comp hpair
  simpa [coordinateDerivative, Function.comp_def] using hcomp

theorem coordinateDerivative_mul_coordinateDerivative {n : ℕ}
    {f φ : (Fin n → ℝ) → ℝ} (hcont_f : ContDiff ℝ 1 f)
    (hcont_φ : ContDiff ℝ 2 φ) (i k : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative
        (fun y => f y * coordinateDerivative φ i y) k x =
      coordinateDerivative f k x * coordinateDerivative φ i x +
        f x * coordinateDerivative (fun y => coordinateDerivative φ i y) k x := by
  exact coordinateDerivative_mul hcont_f (contDiff_coordinateDerivative hcont_φ i) k x

theorem cylindricalDerivative_inner_eq_covariance {n : ℕ}
    {h : Fin n → SpaceTime → ℝ} (hmem : ∀ i, MemLp (h i) 2)
    (a b : Fin n → ℝ) :
    ∫ z, (∑ i, a i * h i z) * (∑ j, b j * h j z) =
      ∑ i, ∑ j, a i * b j * ∫ z, h i z * h j z := by
  have hsum : ∀ z : SpaceTime,
      (∑ i, a i * h i z) * (∑ j, b j * h j z) =
        ∑ i, ∑ j, (a i * b j) * (h i z * h j z) := by
    intro z
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hsum]
  calc
    ∫ z, ∑ i, ∑ j, a i * b j * (h i z * h j z) =
        ∑ i, ∫ z, ∑ j, a i * b j * (h i z * h j z) := by
      apply integral_finsetSum
      intro i hi
      apply integrable_finsetSum
      intro j hj
      exact (hmem i).integrable_mul (hmem j) |>.const_mul _
    _ = ∑ i, ∑ j, a i * b j * ∫ z, h i z * h j z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul]
      · intro j hj
        exact (hmem i).integrable_mul (hmem j) |>.const_mul _

end RegularityStructures

end
