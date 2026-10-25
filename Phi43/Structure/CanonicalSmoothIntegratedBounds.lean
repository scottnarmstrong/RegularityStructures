/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothTaylorBounds
public import Phi43.Structure.CanonicalTaylorConvolutionSpatial
public import Phi43.Structure.CanonicalSmoothCancellation
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The higher-order integrated Psi bound

The auxiliary symbol `I(Ψ)` has degree strictly between one and two.
Its genuine first-spatial Taylor subtraction yields the corresponding
local bound. This is an ingredient of the canonical Gamma estimate in
Hairer [Hai14, Proposition 8.27].
-/

public noncomputable section

namespace RegularityStructures.Phi43

open scoped ContDiff in
/-- The auxiliary integrated Psi has its full homogeneity bound, including
the first-spatial cancellation, locally uniformly in the base point. -/
theorem canonicalPi_iPsi_local_bound (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y : ParabolicSpace,
      parabolicNorm (y - x) ≤ 1 →
        |(hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .iPsi) y| ≤
          C * parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hf : ContDiff ℝ ∞ D.localPsi := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact canonicalGlobalPiBasis_smooth N noise .psi
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  have h1 : 1 < homogeneity κ .iPsi := by simp only [homogeneity]; linarith
  have h2 : homogeneity κ .iPsi ≤ 2 := by simp only [homogeneity]; linarith
  have h0 : 0 < homogeneity κ .iPsi := zero_lt_one.trans h1
  obtain ⟨C, hC0, hC⟩ := canonicalSmooth_compact_taylor_bound
    (contDiff_hairerConvolution N hf) hS h0
  refine ⟨C, hC0, fun x hx y hxy => ?_⟩
  have he : D.canonicalPi x (basis .iPsi) y =
      taylorProfile (hairerConvolution N D.localPsi) (homogeneity κ .iPsi) (y - x) x := by
    rw [CanonicalData.canonicalPi_basis]
    change hairerConvolution N D.localPsi y -
      ((if 0 < homogeneity κ .iPsi then hairerConvolution N D.localPsi x else 0) +
        (if 1 < homogeneity κ .iPsi then ∑ i : Fin 3,
          hairerSpatialGradient N D.localPsi i x *
            (parabolicCoords y i.succ - parabolicCoords x i.succ) else 0)) = _
    simp only [h0, h1, ite_true]
    rw [hairerTaylorProfile_eq_firstSpatial N hf h1 h2]
    ring
  change |D.canonicalPi x (basis .iPsi) y| ≤ _
  rw [he]
  exact hC x hx (y - x) hxy

/-- The constant integrated-Psi transition coefficient is the actual based
Taylor remainder. This follows from canonical covariance and base cancellation. -/
theorem canonicalGamma_cPsi_eq_iPsi (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (x y : ParabolicSpace) :
    ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsi =
      (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .iPsi) y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hκ := κ.property.2
  have hi : 0 < homogeneity κ .iPsi := by simp only [homogeneity]; linarith
  have hzero := canonicalPi_positive_at_base N κ noise .iPsi hi y
  have hh := congrFun (D.canonicalPi_gamma y x (basis .iPsi)) y
  change D.canonicalPi y (structureGroupMap (D.canonicalGammaParameter y x) (basis .iPsi)) y =
    D.canonicalPi x (basis .iPsi) y at hh
  simp only [structureGroupMap_basis, structureBasisAction, primitiveAction, map_add,
    map_smul, map_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    CanonicalData.canonicalPi_one, CanonicalData.canonicalPi_x,
    CanonicalData.relCoord, sub_self, mul_zero, Finset.sum_const_zero, add_zero,
    mul_one] at hh
  change D.canonicalPi y (basis .iPsi) y = 0 at hzero
  rw [hzero, zero_add] at hh
  exact hh

/-- The higher-order constant character coefficient satisfies its required
local homogeneity bound without any whole-space growth assumption. -/
theorem canonicalGamma_cPsi_local_bound (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y : ParabolicSpace,
      parabolicNorm (y - x) ≤ 1 →
        |((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsi| ≤
          C * parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
  obtain ⟨C, hC0, hC⟩ := canonicalPi_iPsi_local_bound N κ noise hS
  refine ⟨C, hC0, fun x hx y hxy => ?_⟩
  rw [canonicalGamma_cPsi_eq_iPsi]
  exact hC x hx y hxy

end RegularityStructures.Phi43

end
