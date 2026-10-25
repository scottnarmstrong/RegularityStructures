/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalCharacterGrowthAlgebra
public import Phi43.Structure.CanonicalGlobalDerivativeGrowth
import RegularityStructures.Abstract.Integration.Theorem512.Helpers
public import Phi43.Structure.CanonicalSmoothCharacters

/-!
# Polynomial growth of the actual canonical character coefficients

Hairer [Hai14, (8.20), Proposition 8.27], under the polynomial
derivative-growth hypothesis of the weighted framework [Hos25, Definition 2.1].
The characters are the actual convolution and gradient values. Their growth
is derived from the global trees and finite character algebra.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- Every coefficient of the actual base-point character action grows at
most polynomially, as a consequence of the noise's derivative envelope. -/
theorem canonicalStructureGroup_coeff_growth (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p)
    (τ σ : Symbol) :
    PolyBounded (fun z => structureGroupMap
      ((hairerCanonicalData (κ := κ) N noise).canonicalCharacter z) (basis τ) σ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hn := canonicalNoise_polyBounded_of_derivatives noise C p hg
  have hglob := canonicalGlobalPiBasis_growth N (κ := κ) noise hn
  have hder := canonicalGlobalPiBasis_derivative_growth N κ noise C p hg
  have hsmooth := canonicalGlobalPiBasis_smooth N (κ := κ) noise
  have hcoord (i : Fin 4) : PolyBounded (fun z => parabolicCoords z i) := by
    fin_cases i
    · exact hglob .x0
    · exact hglob (.x 0)
    · exact hglob (.x 1)
    · exact hglob (.x 2)
  have hx (i : Fin 4) : PolyBounded (fun z => (D.canonicalCharacter z).shift i) := by
    simpa only [CanonicalData.canonicalCharacter, CanonicalData.canonicalShift, neg_one_mul] using
      (hcoord i).const_mul (-1)
  have hgrad (i : Fin 3) : PolyBounded (hairerSpatialGradient N D.globalPsi i) := by
    have hm := (continuous_hairerSpatialGradient N (hsmooth .psi) i).measurable
    have hdf : PolyBounded (fun z => ‖fderiv ℝ (hairerConvolution N D.globalPsi) z‖) :=
      hder .iPsi
    apply canonicalPolyBounded_of_domination hm
      (hdf.const_mul ‖(((0 : ℝ), Pi.single i (1 : ℝ)) : ParabolicSpace)‖)
    intro z
    rw [hairerSpatialGradient_eq_fderiv N (hsmooth .psi) i]
    change |fderiv ℝ (hairerConvolution N D.globalPsi) z (0, Pi.single i 1)| ≤
      |‖(((0 : ℝ), Pi.single i (1 : ℝ)) : ParabolicSpace)‖ *
        ‖fderiv ℝ (hairerConvolution N D.globalPsi) z‖|
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    simpa only [Real.norm_eq_abs, mul_comm] using
      (fderiv ℝ (hairerConvolution N D.globalPsi) z).le_opNorm (0, Pi.single i 1)
  have hpg (i : Fin 3) : PolyBounded (fun z => (D.canonicalCharacter z).cPsiGrad i) := by
    change PolyBounded (fun z => -hairerSpatialGradient N D.localPsi i z)
    rw [CanonicalData.localPsi_eq_globalPsi]
    simpa only [neg_one_mul] using (hgrad i).const_mul (-1)
  have hp : PolyBounded (fun z => (D.canonicalCharacter z).cPsi) := by
    change PolyBounded (fun z => -hairerConvolution N D.localPsi z +
      ∑ i, (D.canonicalCharacter z).shift i.succ * (D.canonicalCharacter z).cPsiGrad i)
    have hsum : PolyBounded (fun z =>
        ∑ i : Fin 3, (D.canonicalCharacter z).shift i.succ * (D.canonicalCharacter z).cPsiGrad i) := by
      simpa only [one_mul, Pi.mul_apply] using PolyBounded.finsetSum Finset.univ
        (fun _ : Fin 3 => (1 : ℝ)) _
        (fun i _ => canonicalPolyBounded_mul (hx i.succ) (hpg i))
    rw [CanonicalData.localPsi_eq_globalPsi]
    have hi : PolyBounded (fun z => -hairerConvolution N D.globalPsi z) := by
      simpa only [neg_one_mul] using! (hglob .iPsi).const_mul (-1)
    exact hi.add hsum
  have hs : PolyBounded (fun z => (D.canonicalCharacter z).cPsiSq) := by
    change PolyBounded (fun z => -hairerConvolution N D.localPsiSq z)
    rw [CanonicalData.localPsiSq_eq_globalPsiSq]
    simpa only [neg_one_mul] using! (hglob .iPsiSq).const_mul (-1)
  have hc : PolyBounded (fun z => (D.canonicalCharacter z).cPsiCube) := by
    change PolyBounded (fun z => -hairerConvolution N D.localPsiCube z)
    rw [CanonicalData.localPsiCube_eq_globalPsiCube]
    simpa only [neg_one_mul] using! (hglob .iPsiCube).const_mul (-1)
  exact polyBounded_structureGroup_coeff κ D.canonicalCharacter hx hp hpg hs hc τ σ
    (continuous_canonicalStructureGroup_coeff N noise τ σ).measurable

end RegularityStructures.Phi43

end
