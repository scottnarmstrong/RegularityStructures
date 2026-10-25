/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureDivergence
public import RegularityStructures.Probability.MalliavinClosureGaussianIBP

/-!
# Gaussian representation of the cylindrical divergence identity

This module supplies the coordinate integration-by-parts hypotheses in the finite-dimensional
divergence calculation from the square-root representation of a centred Gaussian vector.  The
growth and integrability assumptions for each product `f ∂ᵢ φ`, including its transformed and
density versions, remain explicit.  This is the finite-dimensional random-test identity used in
the closability argument for the cylindrical Malliavin derivative; compare [HS23,
Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem gaussian_gradient_duality_of_standard_representation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Ω → Fin n → ℝ} {C A : Matrix (Fin n) (Fin n) ℝ}
    {f φ : (Fin n → ℝ) → ℝ}
    (hX : IsCentredGaussianVector P X C)
    (hAsymm : A.IsSymm) (hAsq : A * A = C)
    (hlaw : P.map X = (standardGaussianMeasure n).map
      (Matrix.mulVecLin A))
    (hcont_f : ContDiff ℝ 1 f) (hcont_φ : ContDiff ℝ 2 φ)
    (_hgrowth_f : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_u : ∀ i, ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ,
        |f x * coordinateDerivative φ i x| +
          ‖fderiv ℝ (fun y => f y * coordinateDerivative φ i y) x‖ ≤
            K * (1 + ‖x‖) ^ M)
    (hgrowth_u_transformed : ∀ i, ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ z : Fin n → ℝ,
        |f (Matrix.mulVec A z) * coordinateDerivative φ i (Matrix.mulVec A z)| +
          ‖fderiv ℝ (fun y =>
            f (Matrix.mulVec A y) * coordinateDerivative φ i (Matrix.mulVec A y)) z‖ ≤
            K * (1 + ‖z‖) ^ M)
    (hint_u : ∀ i, Integrable
      (fun ω => f (X ω) * coordinateDerivative φ i (X ω)) P)
    (hint_du : ∀ i k, Integrable
      (fun ω => coordinateDerivative
        (fun y => f y * coordinateDerivative φ i y) k (X ω)) P)
    (hint_xu : ∀ i k, Integrable
      (fun ω => X ω k * (f (X ω) * coordinateDerivative φ i (X ω))) P)
    (hint_u_std : ∀ i, Integrable
      (fun z : Fin n → ℝ =>
        f (Matrix.mulVec A z) * coordinateDerivative φ i (Matrix.mulVec A z))
      (standardGaussianMeasure n))
    (hint_du_std : ∀ i k, Integrable
      (fun z : Fin n → ℝ => coordinateDerivative
        (fun y => f y * coordinateDerivative φ i y) k (Matrix.mulVec A z))
      (standardGaussianMeasure n))
    (hint_xu_std : ∀ i k, Integrable
      (fun z : Fin n → ℝ => z k *
        (f (Matrix.mulVec A z) * coordinateDerivative φ i (Matrix.mulVec A z)))
      (standardGaussianMeasure n))
    (hint_u_density : ∀ i, Integrable
      (fun z : Fin n → ℝ =>
        f (Matrix.mulVec A z) * coordinateDerivative φ i (Matrix.mulVec A z) *
          standardGaussianDensityReal z) volume)
    (hint_du_density : ∀ i k, Integrable
      (fun z : Fin n → ℝ => coordinateDerivative
        (fun y => f y * coordinateDerivative φ i y) k (Matrix.mulVec A z) *
          standardGaussianDensityReal z) volume)
    (hint_xu_density : ∀ i k, Integrable
      (fun z : Fin n → ℝ => z k *
        (f (Matrix.mulVec A z) * coordinateDerivative φ i (Matrix.mulVec A z)) *
          standardGaussianDensityReal z) volume)
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
  have hparts : ∀ i, ∫ ω, X ω i *
      (f (X ω) * coordinateDerivative φ i (X ω)) ∂P =
      ∑ k, C i k * ∫ ω, coordinateDerivative
        (fun y => f y * coordinateDerivative φ i y) k (X ω) ∂P := by
    intro i
    let u : (Fin n → ℝ) → ℝ := fun y => f y * coordinateDerivative φ i y
    have hcont_u : ContDiff ℝ 1 u := by
      dsimp [u]
      exact hcont_f.mul (contDiff_coordinateDerivative hcont_φ i)
    have hu := gaussian_vector_integration_by_parts_of_standard_representation
      hX hAsymm hAsq hlaw hcont_u (hgrowth_u i) (hgrowth_u_transformed i)
      (by simpa [u] using hint_u i)
      (by
        intro k
        simpa [u] using hint_du i k)
      (by
        intro k
        simpa [u] using hint_xu i k)
      (by simpa [u] using hint_u_std i)
      (by
        intro k
        simpa [u] using hint_du_std i k)
      (by
        intro k
        simpa [u] using hint_xu_std i k)
      (by simpa [u] using hint_u_density i)
      (by
        intro k
        simpa [u] using hint_du_density i k)
      (by
        intro k
        simpa [u] using hint_xu_density i k)
    simpa [u] using hu i
  exact gaussian_gradient_duality_of_coordinate_ibp hcont_f hcont_φ hparts
    hint_left hint_A hint_B hint_hess

end RegularityStructures

end
