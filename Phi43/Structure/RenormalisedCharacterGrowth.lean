/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalCharacterGrowth
public import Phi43.Structure.RenormalisedExtensionContinuity
import Mathlib.Tactic.FinCases

/-!
# Polynomial growth of the corrected character

The corrected character differs from the canonical one only in its integrated
cubic coordinate, by the explicit term `3 C₁ K * Ψ`.  Hence the finite
structure-group action still has polynomially growing coefficients under the
same source-only derivative premise [Hai14, (9.4c), Proposition 8.27].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

theorem renormalisedExtensionStructureGroup_coeff_growth (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (τ σ : Symbol) :
    PolyBounded (fun z => structureGroupMap
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter C z)
        (basis τ) σ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hn := canonicalNoise_polyBounded_of_derivatives noise Cg q hg
  have hglob := canonicalGlobalPiBasis_growth N (κ := κ) noise hn
  have hshift (i : Fin 4) : PolyBounded (fun z => (D.renormalisedExtensionCharacter C z).shift i) := by
    fin_cases i
    · change PolyBounded (fun z => -D.globalPiBasis .x0 z)
      simpa only [CanonicalData.globalPiBasis, neg_one_mul] using (hglob .x0).const_mul (-1)
    · change PolyBounded (fun z => -D.globalPiBasis (.x 0) z)
      simpa only [CanonicalData.globalPiBasis, neg_one_mul] using (hglob (.x 0)).const_mul (-1)
    · change PolyBounded (fun z => -D.globalPiBasis (.x 1) z)
      simpa only [CanonicalData.globalPiBasis, neg_one_mul] using (hglob (.x 1)).const_mul (-1)
    · change PolyBounded (fun z => -D.globalPiBasis (.x 2) z)
      simpa only [CanonicalData.globalPiBasis, neg_one_mul] using (hglob (.x 2)).const_mul (-1)
  have hder := canonicalGlobalPiBasis_derivative_growth N κ noise Cg q hg
  have hsmooth := canonicalGlobalPiBasis_smooth N (κ := κ) noise
  have hgrad0 (i : Fin 3) : PolyBounded (fun z =>
      (D.canonicalCharacter z).cPsiGrad i) := by
    change PolyBounded (fun z => -hairerSpatialGradient N D.localPsi i z)
    rw [CanonicalData.localPsi_eq_globalPsi]
    have hm := (continuous_hairerSpatialGradient N (hsmooth .psi) i).measurable
    have hdf : PolyBounded (fun z => ‖fderiv ℝ (hairerConvolution N D.globalPsi) z‖) :=
      hder .iPsi
    have hpos : PolyBounded (fun z => hairerSpatialGradient N D.globalPsi i z) := by
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
    simpa only [neg_one_mul] using hpos.const_mul (-1)
  have hgrad (i : Fin 3) : PolyBounded (fun z =>
      (D.canonicalCharacter z).cPsiGrad i) := hgrad0 i
  have hpg : ∀ i, PolyBounded (fun z =>
      (D.renormalisedExtensionCharacter C z).cPsiGrad i) := by
    intro i
    simpa only [CanonicalData.renormalisedExtensionCharacter] using hgrad i
  have hs : PolyBounded (fun z => (D.canonicalCharacter z).cPsiSq) := by
    change PolyBounded (fun z => -hairerConvolution N D.localPsiSq z)
    rw [CanonicalData.localPsiSq_eq_globalPsiSq]
    simpa only [neg_one_mul] using! (hglob .iPsiSq).const_mul (-1)
  have hs' : PolyBounded (fun z =>
      (D.renormalisedExtensionCharacter C z).cPsiSq) := by
    simpa only [CanonicalData.renormalisedExtensionCharacter] using hs
  have hp : PolyBounded (fun z => (D.canonicalCharacter z).cPsi) := by
    change PolyBounded (fun z => -hairerConvolution N D.localPsi z +
      ∑ i, (D.canonicalCharacter z).shift i.succ * (D.canonicalCharacter z).cPsiGrad i)
    rw [CanonicalData.localPsi_eq_globalPsi]
    have hsum : PolyBounded (fun z =>
        ∑ i : Fin 3, (D.canonicalCharacter z).shift i.succ *
          (D.canonicalCharacter z).cPsiGrad i) := by
      have hsh (i : Fin 3) : PolyBounded (fun z =>
          (D.canonicalCharacter z).shift i.succ) := by
        simpa only [CanonicalData.renormalisedExtensionCharacter,
          CanonicalData.canonicalCharacter] using (hshift i.succ)
      simpa only [one_mul, Pi.mul_apply] using PolyBounded.finsetSum Finset.univ
        (fun _ : Fin 3 => (1 : ℝ)) _
        (fun i _ => canonicalPolyBounded_mul (hsh i) (hgrad i))
    have hi : PolyBounded (fun z => -hairerConvolution N D.globalPsi z) := by
      simpa only [neg_one_mul] using! (hglob .iPsi).const_mul (-1)
    exact hi.add hsum
  have hp' : PolyBounded (fun z =>
      (D.renormalisedExtensionCharacter C z).cPsi) := by
    simpa only [CanonicalData.renormalisedExtensionCharacter] using hp
  have hc0 : PolyBounded (fun z => (D.canonicalCharacter z).cPsiCube) := by
    change PolyBounded (fun z => -hairerConvolution N D.localPsiCube z)
    rw [CanonicalData.localPsiCube_eq_globalPsiCube]
    simpa only [neg_one_mul] using! (hglob .iPsiCube).const_mul (-1)
  have hc : PolyBounded (fun z =>
      (D.renormalisedExtensionCharacter C z).cPsiCube) := by
    have hi := hglob .iPsi
    have hcc : PolyBounded (fun z => (D.canonicalCharacter z).cPsiCube) := by
      exact hc0
    have he : (fun z => (D.renormalisedExtensionCharacter C z).cPsiCube) =
        fun z => (D.canonicalCharacter z).cPsiCube +
          3 * C₁ C * D.globalIPsi z := by
      funext z
      rfl
    rw [he]
    exact hcc.add (hi.const_mul (3 * C₁ C))
  apply polyBounded_structureGroup_coeff κ
    (fun z => D.renormalisedExtensionCharacter C z) hshift hp' hpg hs' hc τ σ
  exact (continuous_renormalisedExtensionStructureGroup_coeff N noise C τ σ).measurable

end RegularityStructures.Phi43

end
