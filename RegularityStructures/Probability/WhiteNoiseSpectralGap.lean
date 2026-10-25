/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPoincareCovariance
public import RegularityStructures.Probability.SpectralGap
public import RegularityStructures.Probability.CylindricalFunctional

/-!
# The white-noise spectral gap for cylindrical functionals

For a cylindrical functional, the finite family of white-noise coordinates is a centred Gaussian
vector with the `L²` covariance matrix.  The covariance-form Gaussian Poincare theorem therefore
feeds directly into the cylindrical derivative identity.  This is the spectral-gap input in
[HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem whiteNoise_cylindrical_spectral_gap {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hW : IsWhiteNoise P W) (hmem : ∀ i, MemLp (h i) 2)
    (hcont : ContDiff ℝ 1 f)
    (hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M) :
    Var[cylindricalFunctional W h f; P] ≤
      ∫ ω, (∫ z, (cylindricalDerivative W h f ω z) ^ 2
        ∂(volume : Measure SpaceTime)) ∂P := by
  apply cylindrical_spectral_gap_reduction hW hmem hcont
  have hX := hW.2 n h hmem
  rw [variance_map hcont.continuous.measurable.aemeasurable hX.1]
  simpa [Function.comp_def] using
    gaussian_poincare_centredGaussianVector hX hcont hgrowth

end RegularityStructures

end
