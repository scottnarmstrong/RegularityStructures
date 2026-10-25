/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureDivergenceAlgebra

/-!
# Finite-dimensional cylindrical divergence identity

This module performs the algebraic cancellation in the random-test integration-by-parts formula.
The coordinate identities supplied by Gaussian integration by parts are kept as explicit theorem
arguments; the result then identifies the gradient pairing with the Gaussian divergence of a
cylindrical test derivative.  This is the finite-dimensional analytic interface needed for the
closability step in [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

def cylindricalGradientEnergy {n : ℕ} (C : Fin n → Fin n → ℝ)
    (a b : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ k, C i k * a k * b i

def coordinateHessian {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (i k : Fin n) (x : Fin n → ℝ) : ℝ :=
  coordinateDerivative (fun y => coordinateDerivative φ i y) k x

def cylindricalGaussianDivergence {n : ℕ} (C : Fin n → Fin n → ℝ)
    (f φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  f x * (∑ i, x i * coordinateDerivative φ i x -
    ∑ i, ∑ k, C i k * coordinateHessian φ i k x)

theorem gaussian_gradient_duality_of_coordinate_ibp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    {f φ : (Fin n → ℝ) → ℝ}
    (hcont_f : ContDiff ℝ 1 f) (hcont_φ : ContDiff ℝ 2 φ)
    (hparts : ∀ i, ∫ ω, X ω i * (f (X ω) * coordinateDerivative φ i (X ω)) ∂P =
      ∑ k, C i k * ∫ ω, coordinateDerivative
        (fun y => f y * coordinateDerivative φ i y) k (X ω) ∂P)
    (hint_left : ∀ i, Integrable
      (fun ω => f (X ω) * (X ω i * coordinateDerivative φ i (X ω))) P)
    (hint_A : ∀ i k, Integrable
      (fun ω => coordinateDerivative f k (X ω) * coordinateDerivative φ i (X ω)) P)
    (hint_B : ∀ i k, Integrable
      (fun ω => f (X ω) * coordinateHessian φ i k (X ω)) P)
    (hint_hess : ∀ i k, Integrable
      (fun ω => f (X ω) * (C i k * coordinateHessian φ i k (X ω))) P) :
    ∫ ω, cylindricalGradientEnergy C
        (fun i => coordinateDerivative f i (X ω))
        (fun i => coordinateDerivative φ i (X ω)) ∂P =
      ∫ ω, cylindricalGaussianDivergence C f φ (X ω) ∂P := by
  have hprod (i k : Fin n) (x : Fin n → ℝ) :
      coordinateDerivative (fun y => f y * coordinateDerivative φ i y) k x =
        coordinateDerivative f k x * coordinateDerivative φ i x +
          f x * coordinateHessian φ i k x := by
    exact coordinateDerivative_mul_coordinateDerivative hcont_f hcont_φ i k x
  have hparts' (i : Fin n) :
      ∫ ω, X ω i * (f (X ω) * coordinateDerivative φ i (X ω)) ∂P =
        ∑ k, C i k *
          (∫ ω, coordinateDerivative f k (X ω) * coordinateDerivative φ i (X ω) ∂P +
            ∫ ω, f (X ω) * coordinateHessian φ i k (X ω) ∂P) := by
    rw [hparts i]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    have heq : (fun ω => coordinateDerivative
        (fun y => f y * coordinateDerivative φ i y) k (X ω)) =ᵐ[P]
        (fun ω => coordinateDerivative f k (X ω) * coordinateDerivative φ i (X ω) +
          f (X ω) * coordinateHessian φ i k (X ω)) := by
      filter_upwards [] with ω
      exact hprod i k (X ω)
    rw [integral_congr_ae heq, integral_add (hint_A i k) (hint_B i k)]
  have hleft_sum :
      ∑ i, ∫ ω, f (X ω) * (X ω i * coordinateDerivative φ i (X ω)) ∂P =
        ∑ i, ∑ k, C i k *
          (∫ ω, coordinateDerivative f k (X ω) * coordinateDerivative φ i (X ω) ∂P +
            ∫ ω, f (X ω) * coordinateHessian φ i k (X ω) ∂P) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hleft : ∫ ω, f (X ω) * (X ω i * coordinateDerivative φ i (X ω)) ∂P =
        ∫ ω, X ω i * (f (X ω) * coordinateDerivative φ i (X ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    rw [hleft, hparts' i]
  have henergy :
      ∫ ω, cylindricalGradientEnergy C
          (fun i => coordinateDerivative f i (X ω))
          (fun i => coordinateDerivative φ i (X ω)) ∂P =
        ∑ i, ∑ k, C i k *
          ∫ ω, coordinateDerivative f k (X ω) * coordinateDerivative φ i (X ω) ∂P := by
    unfold cylindricalGradientEnergy
    have hEA (i k : Fin n) : Integrable
        (fun ω => C i k * coordinateDerivative f k (X ω) *
          coordinateDerivative φ i (X ω)) P := by
      have h := (hint_A i k).const_mul (C i k)
      exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      · intro k hk
        exact hEA i k
    · intro i hi
      apply integrable_finsetSum
      intro k hk
      exact hEA i k
  have hdiv :
      ∫ ω, cylindricalGaussianDivergence C f φ (X ω) ∂P =
        ∑ i, ∫ ω, f (X ω) * (X ω i * coordinateDerivative φ i (X ω)) ∂P -
          ∑ i, ∑ k, C i k *
            ∫ ω, f (X ω) * coordinateHessian φ i k (X ω) ∂P := by
    have hleft_integral :
        ∫ ω, f (X ω) * (∑ i, X ω i * coordinateDerivative φ i (X ω)) ∂P =
          ∑ i, ∫ ω, f (X ω) * (X ω i * coordinateDerivative φ i (X ω)) ∂P := by
      have hfun : (fun ω => f (X ω) *
          (∑ i, X ω i * coordinateDerivative φ i (X ω))) =
          (fun ω => ∑ i, f (X ω) *
            (X ω i * coordinateDerivative φ i (X ω))) := by
        funext ω
        rw [Finset.mul_sum]
      rw [hfun, integral_finsetSum]
      intro i hi
      exact hint_left i
    have hleft_integrable : Integrable (fun ω => f (X ω) *
        (∑ i, X ω i * coordinateDerivative φ i (X ω))) P := by
      have hfun : (fun ω => f (X ω) *
          (∑ i, X ω i * coordinateDerivative φ i (X ω))) =
          (fun ω => ∑ i, f (X ω) *
            (X ω i * coordinateDerivative φ i (X ω))) := by
        funext ω
        rw [Finset.mul_sum]
      rw [hfun]
      apply integrable_finsetSum
      intro i hi
      exact hint_left i
    have hhess_integral :
        ∫ ω, f (X ω) * (∑ i, ∑ k, C i k * coordinateHessian φ i k (X ω)) ∂P =
          ∑ i, ∑ k, ∫ ω, f (X ω) *
            (C i k * coordinateHessian φ i k (X ω)) ∂P := by
      have hfun : (fun ω => f (X ω) *
          (∑ i, ∑ k, C i k * coordinateHessian φ i k (X ω))) =
          (fun ω => ∑ i, ∑ k, f (X ω) *
            (C i k * coordinateHessian φ i k (X ω))) := by
        funext ω
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      rw [hfun, integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro k hk
        exact hint_hess i k
      · intro i hi
        apply integrable_finsetSum
        intro k hk
        exact hint_hess i k
    have hhess_integrable : Integrable (fun ω => f (X ω) *
        (∑ i, ∑ k, C i k * coordinateHessian φ i k (X ω))) P := by
      have hfun : (fun ω => f (X ω) *
          (∑ i, ∑ k, C i k * coordinateHessian φ i k (X ω))) =
          (fun ω => ∑ i, ∑ k, f (X ω) *
            (C i k * coordinateHessian φ i k (X ω))) := by
        funext ω
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      rw [hfun]
      apply integrable_finsetSum
      intro i hi
      apply integrable_finsetSum
      intro k hk
      exact hint_hess i k
    have hpoint : (fun ω => cylindricalGaussianDivergence C f φ (X ω)) =ᵐ[P]
        (fun ω => f (X ω) * (∑ i, X ω i * coordinateDerivative φ i (X ω)) -
          f (X ω) * (∑ i, ∑ k, C i k * coordinateHessian φ i k (X ω))) := by
      filter_upwards [] with ω
      unfold cylindricalGaussianDivergence
      ring
    rw [integral_congr_ae hpoint, integral_sub hleft_integrable hhess_integrable,
      hleft_integral, hhess_integral]
    apply congrArg₂ (fun x y : ℝ => x - y)
    · rfl
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      have heq :
          (∫ ω, f (X ω) * (C i k * coordinateHessian φ i k (X ω)) ∂P) =
            C i k * ∫ ω, f (X ω) * coordinateHessian φ i k (X ω) ∂P := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      rw [heq]
  rw [henergy]
  rw [hdiv]
  rw [hleft_sum]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

end RegularityStructures

end
