/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalGlobalSpatialGradientGrowth
public import Phi43.Structure.CanonicalFiniteEnvelopes
public import Phi43.Structure.CanonicalGammaPrimitiveBounds
public import Phi43.Structure.CanonicalLocalDerivativeEnvelope

/-!
# A weighted spatial-gradient character estimate

This is the integrated spatial-gradient component of the global structure-group
bound for the enlarged smooth canonical model. It is a source-derived part of
Hairer [Hai14, Proposition 8.27], in the polynomially weighted formulation of
[Hos25, Definition 2.1].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped ContDiff

private theorem hairerSpatialGradient_localPsi_smooth
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (i : Fin 3) :
    ContDiff ℝ ∞ (hairerSpatialGradient N
      (hairerCanonicalData (κ := κ) N noise).localPsi i) := by
  rw [CanonicalData.localPsi_eq_globalPsi]
  have he : hairerSpatialGradient N
      (hairerCanonicalData (κ := κ) N noise).globalPsi i =
      fun z => fderiv ℝ
        (hairerConvolution N (hairerCanonicalData (κ := κ) N noise).globalPsi) z
        (0, Pi.single i 1) :=
    funext (hairerSpatialGradient_eq_fderiv N
      (canonicalGlobalPiBasis_smooth N noise .psi) i)
  rw [he]
  exact ((contDiff_hairerConvolution N
      (canonicalGlobalPiBasis_smooth N noise .psi)).fderiv_right (by simp)).clm_apply
    contDiff_const

/-- The actual cPsiGrad coefficient has the expected polynomially weighted
local homogeneity bound. -/
theorem canonicalGamma_cPsiGrad_growth
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ p : ℕ, ∀ i : Fin 3, ∀ x y,
      parabolicNorm (y - x) ≤ 1 →
        |((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiGrad i| ≤
          B * (1 + parabolicNorm x)^p *
            parabolicNorm (y - x)^(homogeneity κ .iPsi - 1) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hsp (i : Fin 3) : PolyBounded (fun z => ‖fderiv ℝ
      (phi43SpatialDerivative D.globalPsi i) z‖) := by
    have heq : phi43SpatialDerivative D.globalPsi i =
        hairerSpatialGradient N noise.zeta i := by
      funext z
      unfold phi43SpatialDerivative
      rw [hairerSpatialGradient_eq_fderiv N noise.smooth i]
      rfl
    rw [heq]
    exact canonicalGlobalSpatialGradient_fderiv_growth N κ noise C q hg i
  have hgrad (i : Fin 3) : PolyBounded (fun z =>
      ‖fderiv ℝ (hairerSpatialGradient N D.globalPsi i) z‖) :=
    canonicalPolyBounded_fderiv_hairerSpatialGradient N
      (canonicalGlobalPiBasis_smooth (κ := κ) N noise .psi) i (hsp i)
  obtain ⟨A, hA0, p, hA⟩ := canonicalPolyBounded_finite_envelope
    (fun i : Fin 3 => fun z =>
      ‖fderiv ℝ (hairerSpatialGradient N D.globalPsi i) z‖) hgrad
  have hα0 : 0 ≤ homogeneity κ .iPsi - 1 := by
    simp only [homogeneity]
    linarith [κ.property.1, κ.property.2]
  have hα1 : homogeneity κ .iPsi - 1 ≤ 1 := by
    simp only [homogeneity]
    linarith [κ.property.1, κ.property.2]
  refine ⟨A * 5 ^ p, mul_nonneg hA0 (by positivity), p, ?_⟩
  intro i x y hxy
  have hder : ∀ z, ‖fderiv ℝ (hairerSpatialGradient N D.globalPsi i) z‖ ≤
      A * (1 + parabolicNorm z) ^ p := fun z =>
    by simpa only [abs_of_nonneg (norm_nonneg _)] using hA i z
  have hderLocal : ∀ z, ‖fderiv ℝ
      (hairerSpatialGradient N
        D.localPsi i) z‖ ≤
      A * (1 + parabolicNorm z) ^ p := by
    rw [CanonicalData.localPsi_eq_globalPsi D]
    exact hder
  have hinc := canonicalSmooth_local_increment_of_derivative_bound
    (hairerSpatialGradient_localPsi_smooth N κ noise i) A p hderLocal x y hxy
  have hd : parabolicNorm (y - x) ≤
      parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' (parabolicNorm_nonneg _) hxy hα0 hα1)
  rw [canonicalGamma_cPsiGrad_eq_gradient_sub]
  exact hinc.trans (mul_le_mul_of_nonneg_left hd
    (mul_nonneg (mul_nonneg hA0 (by positivity))
      (pow_nonneg (by linarith [parabolicNorm_nonneg x]) p)))

end RegularityStructures.Phi43

end
