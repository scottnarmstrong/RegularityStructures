/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothIntegratedBounds
public import Phi43.Structure.CanonicalSmoothLocalBounds
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import RegularityStructures.Analysis.Kernel.GeneratorLip
public import RegularityStructures.Analysis.Heat.Annihilating.Translate
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime

/-!
# Local bounds for the primitive canonical transition characters

Ingredients of the Gamma estimate for the canonical model in Hairer
[Hai14, Proposition 8.27]. Every coefficient is the actual convolution
Taylor coefficient; no temporal growth condition is imposed.
-/

public noncomputable section

namespace RegularityStructures.Phi43

open scoped ContDiff in
private theorem gradient_smooth (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (hairerSpatialGradient N f i) := by
  have he : hairerSpatialGradient N f i =
      fun z => fderiv ℝ (hairerConvolution N f) z (0, Pi.single i 1) :=
    funext (hairerSpatialGradient_eq_fderiv N hf i)
  rw [he]
  exact ((contDiff_hairerConvolution N hf).fderiv_right (by simp)).clm_apply contDiff_const

private theorem norm_le_parabolicNorm_small {v : ParabolicSpace}
    (hv : parabolicNorm v ≤ 1) : ‖v‖ ≤ parabolicNorm v := by
  have hs : Real.sqrt |v.1| ≤ parabolicNorm v := by
    unfold parabolicNorm
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have ht : |v.1| ≤ 1 := by
    have hsq := Real.sq_sqrt (abs_nonneg v.1)
    have hsn := Real.sqrt_nonneg |v.1|
    nlinarith
  exact RegularityStructures.norm_le_parabolicNorm ht

/-- The spatial integrated-Psi coefficient is the difference of actual
spatial convolution derivatives. -/
theorem canonicalGamma_cPsiGrad_eq_gradient_sub (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (x y : ParabolicSpace) (i : Fin 3) :
    ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiGrad i =
      hairerSpatialGradient N (hairerCanonicalData (κ := κ) N noise).localPsi i y -
        hairerSpatialGradient N (hairerCanonicalData (κ := κ) N noise).localPsi i x := by
  change -(-hairerSpatialGradient N _ i y) + (-hairerSpatialGradient N _ i x) = _
  ring

open scoped ContDiff in
/-- Uniform local bounds for the spatial integrated-Psi character. -/
theorem canonicalGamma_cPsiGrad_local_bound (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Fin 3, ∀ x ∈ S, ∀ y ∈ S,
      parabolicNorm (y - x) ≤ 1 →
        |((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiGrad i| ≤
          C * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hp : ContDiff ℝ ∞ D.localPsi := by
    rw [CanonicalData.localPsi_eq_globalPsi]
    exact canonicalGlobalPiBasis_smooth N noise .psi
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall (0 : ParabolicSpace)
  have hb (i : Fin 3) : ∃ B : NNReal, LipschitzOnWith B
      (hairerSpatialGradient N D.localPsi i) (Metric.closedBall 0 R) :=
    (gradient_smooth N hp i).contDiffOn.exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  choose B hB using hb
  refine ⟨∑ i : Fin 3, (B i : ℝ), Finset.sum_nonneg (fun i _ => (B i).coe_nonneg), ?_⟩
  intro i x hx y hy hxy
  have hh := (hB i).dist_le_mul y (hR hy) x (hR hx)
  rw [Real.dist_eq, dist_eq_norm] at hh
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  have hα0 : 0 ≤ homogeneity κ .iPsi - 1 := by simp only [homogeneity]; linarith
  have hα1 : homogeneity κ .iPsi - 1 ≤ 1 := by simp only [homogeneity]; linarith
  have hd : ‖y - x‖ ≤ parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) :=
    (norm_le_parabolicNorm_small hxy).trans (by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' (parabolicNorm_nonneg _) hxy hα0 hα1))
  rw [canonicalGamma_cPsiGrad_eq_gradient_sub]
  exact hh.trans (mul_le_mul (Finset.single_le_sum (fun j _ => (B j).coe_nonneg)
    (Finset.mem_univ i)) hd (norm_nonneg _) (Finset.sum_nonneg fun j _ => (B j).coe_nonneg))

/-- The constant integrated-square coefficient is its actual based remainder. -/
theorem canonicalGamma_cPsiSq_eq_iPsiSq (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (x y : ParabolicSpace) :
    ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiSq =
      (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .iPsiSq) y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hκ := κ.property.2
  have hi : 0 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hzero := canonicalPi_positive_at_base N κ noise .iPsiSq hi y
  have hh := congrFun (D.canonicalPi_gamma y x (basis .iPsiSq)) y
  change D.canonicalPi y (structureGroupMap (D.canonicalGammaParameter y x) (basis .iPsiSq)) y =
    D.canonicalPi x (basis .iPsiSq) y at hh
  simp only [structureGroupMap_basis, structureBasisAction, primitiveAction, map_add,
    map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, CanonicalData.canonicalPi_one,
    mul_one] at hh
  change D.canonicalPi y (basis .iPsiSq) y = 0 at hzero
  rw [hzero, zero_add] at hh
  exact hh

/-- The constant integrated-cube coefficient is its actual based remainder. -/
theorem canonicalGamma_cPsiCube_eq_iPsiCube (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (x y : ParabolicSpace) :
    ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiCube =
      (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .iPsiCube) y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hκ := κ.property.2
  have hi : 0 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have hzero := canonicalPi_positive_at_base N κ noise .iPsiCube hi y
  have hh := congrFun (D.canonicalPi_gamma y x (basis .iPsiCube)) y
  change D.canonicalPi y (structureGroupMap (D.canonicalGammaParameter y x) (basis .iPsiCube)) y =
    D.canonicalPi x (basis .iPsiCube) y at hh
  simp only [structureGroupMap_basis, structureBasisAction, primitiveAction, map_add,
    map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, CanonicalData.canonicalPi_one,
    mul_one] at hh
  change D.canonicalPi y (basis .iPsiCube) y = 0 at hzero
  rw [hzero, zero_add] at hh
  exact hh

/-- Both remaining integrated constant characters obey their actual
homogeneity bounds locally uniformly on every compact set. -/
theorem canonicalGamma_integrated_constants_local_bound (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, parabolicNorm (y - x) ≤ 1 →
      |((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiSq| ≤
        C * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq ∧
      |((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiCube| ≤
        C * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
  obtain ⟨C, hC0, hC⟩ := canonicalPi_positive_local_bound N κ noise hS
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  have hs0 : 0 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hsg : homogeneity κ .iPsiSq < gamma κ := by simp only [homogeneity, gamma]; linarith
  have hc0 : 0 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have hcg : homogeneity κ .iPsiCube < gamma κ := by simp only [homogeneity, gamma]; linarith
  refine ⟨C, hC0, ?_⟩
  intro x hx y hy hxy
  constructor
  · rw [canonicalGamma_cPsiSq_eq_iPsiSq]
    exact hC .iPsiSq hs0 hsg x hx y hy hxy
  · rw [canonicalGamma_cPsiCube_eq_iPsiCube]
    exact hC .iPsiCube hc0 hcg x hx y hy hxy

/-- The polynomial transition is exactly the difference of coordinates. -/
theorem canonicalGamma_shift_eq_coords_sub (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (x y : ParabolicSpace) (i : Fin 4) :
    ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).shift i =
      parabolicCoords y i - parabolicCoords x i := by
  change -(-parabolicCoords y i) + (-parabolicCoords x i) = _
  ring

/-- The canonical polynomial character obeys its parabolic degree bound. -/
theorem canonicalGamma_shift_bound (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (x y : ParabolicSpace) (i : Fin 4) :
    |((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).shift i| ≤
      parabolicNorm (y - x) ^ (parabolicWeight i : ℝ) := by
  rw [canonicalGamma_shift_eq_coords_sub, ← parabolicCoords_sub_apply,
    Real.rpow_natCast]
  exact abs_parabolicCoords_le i

end RegularityStructures.Phi43

end
