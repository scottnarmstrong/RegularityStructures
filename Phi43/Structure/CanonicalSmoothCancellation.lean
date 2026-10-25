/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalKernelHairer
public import Phi43.Structure.CanonicalModel

/-!
# Base-point cancellation of the positive canonical sector

Hairer [Hai14, (8.19)–(8.20), Proposition 8.27]. The actual Taylor
coefficients force every positive retained symbol to vanish at its base
point. This is a local identity, independent of temporal growth.
-/

public noncomputable section

namespace RegularityStructures.Phi43

private theorem integrate_at_base (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    {r : ℝ} (hr : 0 < r) (f : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).integrate r f x x = 0 := by
  simp [CanonicalData.integrate, CanonicalKernel.convolution,
    CanonicalKernel.taylorPolynomial, hr, hairerCanonicalData, hairerCanonicalKernel]

/-- Every positive retained canonical basis element vanishes at the base point. -/
theorem canonicalPi_positive_at_base (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (τ : Symbol) (hτ : 0 < homogeneity κ τ)
    (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis τ) x = 0 := by
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  have hi : 0 < homogeneity κ .iPsi := by simp only [homogeneity]; linarith
  have hs : 0 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hc : 0 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have hi0 := integrate_at_base N κ noise hi
  have hs0 := integrate_at_base N κ noise hs
  have hc0 := integrate_at_base N κ noise hc
  rw [CanonicalData.canonicalPi_basis]
  cases τ with
  | xMul p =>
      refine Sym2.inductionOn p ?_
      intro i j
      simp [CanonicalData.localPiBasis, CanonicalData.localPolynomialQuadratic,
        CanonicalData.relCoord]
  | _ =>
    simp only [homogeneity] at hτ
    all_goals simp [CanonicalData.localPiBasis, CanonicalData.relCoord,
      CanonicalData.localPsiX, CanonicalData.localIPsi, CanonicalData.localIPsiSq,
      CanonicalData.localIPsiCube, CanonicalData.localIPsiPsi,
      CanonicalData.localIPsiPsiSq, CanonicalData.localIPsiSqPsi,
      CanonicalData.localIPsiCubeSq, hi0, hs0, hc0]
    all_goals linarith

end RegularityStructures.Phi43

end
