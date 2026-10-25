/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionLocalBounds
public import Phi43.Structure.RenormalisedExtensionAlgebra
public import Phi43.Structure.CanonicalGammaActionBounds
public import Phi43.Structure.CanonicalGammaPrimitiveBounds

/-!
# Local Gamma bounds for the corrected smooth lift

Only the integrated-cubic primitive transition changes. It equals the
corrected based potential; its derived local bound can therefore be
assembled with the unchanged primitive bounds by the multiplicative
finite group action [Hai14, Theorem 8.44].
-/

public noncomputable section

namespace RegularityStructures.Phi43

theorem renormalisedGamma_cPsiCube_eq (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (x y : ParabolicSpace) :
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).cPsiCube =
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis .iPsiCube) y := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
  have hk0 : 0 < κ.1 := κ.2.1
  have h0 : 0 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have h1 : ¬ 1 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  rw [renormalisedExtensionPi_basis_form]
  change (D.renormalisedExtensionGammaParameter C y x).cPsiCube = D.renormalisedBasedCube C x y
  simp [CanonicalData.renormalisedExtensionGammaParameter,
    CanonicalData.renormalisedExtensionCharacter, structureGroupInv,
    CanonicalData.canonicalCharacter,
    CanonicalData.renormalisedBasedCube, CanonicalData.localIPsiCube,
    CanonicalData.integrate, CanonicalKernel.taylorPolynomial, h0, h1,
    CanonicalData.localPsiCube_eq_globalPsiCube,
    CanonicalKernel.convolution, D, hairerCanonicalData, hairerCanonicalKernel]
  ring

private theorem eq_of_parabolicNorm_sub_eq_zero {x y : ParabolicSpace}
    (h : parabolicNorm (y - x) = 0) : y = x := by
  unfold parabolicNorm at h
  have h1 : 0 ≤ Real.sqrt |(y - x).1| := Real.sqrt_nonneg _
  have h2 : 0 ≤ ∑ i, |(y - x).2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h3 : Real.sqrt |(y - x).1| = 0 := by linarith
  have h4 : ∑ i, |(y - x).2 i| = 0 := by linarith
  have h5 : (y - x).1 = 0 := abs_eq_zero.1 ((Real.sqrt_eq_zero (abs_nonneg _)).1 h3)
  have h6 : ∀ i, (y - x).2 i = 0 := fun i =>
    abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _).1 h4 i
      (Finset.mem_univ i))
  exact sub_eq_zero.1 (Prod.ext h5 (funext h6))

theorem renormalisedGamma_local_bound (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (R : RenormalisationConstants) {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ σ : Symbol,
      homogeneity κ σ < homogeneity κ τ → ∀ x ∈ S, ∀ y ∈ S,
        parabolicNorm (y - x) ≤ 1 →
        |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma R y x (basis τ)) σ| ≤
          C * parabolicNorm (y - x) ^ (homogeneity κ τ - homogeneity κ σ) := by
  obtain ⟨P, hP0, hP⟩ := canonicalGamma_cPsi_local_bound N κ noise hS
  obtain ⟨G, hG0, hG⟩ := canonicalGamma_cPsiGrad_local_bound N κ noise hS
  obtain ⟨B, hB0, hB⟩ := canonicalGamma_integrated_constants_local_bound N κ noise hS
  obtain ⟨E, hE0, hE⟩ := renormalisedExtensionPi_positive_local_bound N κ noise R hS
  let A : ℝ := 1 + P + G + B + E
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have h1A : 1 ≤ A := by dsimp [A]; linarith
  have hPA : P ≤ A := by dsimp [A]; linarith
  have hGA : G ≤ A := by dsimp [A]; linarith
  have hBA : B ≤ A := by dsimp [A]; linarith
  have hEA : E ≤ A := by dsimp [A]; linarith
  let C : ℝ := (1 + 4 * A) + (Fintype.card Symbol : ℝ) ^ 2 * (1 + 4 * A) ^ 2 +
    ((Fintype.card Symbol : ℝ) ^ 2) ^ 2 * (1 + 4 * A) ^ 3
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, fun τ σ hστ x hx y hy hxy => ?_⟩
  by_cases hd : parabolicNorm (y - x) = 0
  · have he := eq_of_parabolicNorm_sub_eq_zero hd
    subst y
    have hne : τ ≠ σ := by intro he; subst σ; exact (lt_irrefl _ hστ)
    rw [CanonicalData.renormalisedExtensionGamma_self]
    simp only [LinearMap.id_apply, basis, Finsupp.single_apply, hne, ite_false, abs_zero]
    exact mul_nonneg hC0 (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  · have hdpos : 0 < parabolicNorm (y - x) := lt_of_le_of_ne (parabolicNorm_nonneg _) (Ne.symm hd)
    let g := (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter R y x
    have hshift (i : Fin 4) : |g.shift i| ≤ A * parabolicNorm (y - x) ^ (parabolicWeight i : ℝ) :=
      (canonicalGamma_shift_bound N κ noise x y i).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg (parabolicNorm_nonneg _) _) h1A)
    have hp : |g.cPsi| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsi :=
      (hP x hx y hxy).trans (mul_le_mul_of_nonneg_right hPA (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
    have hgrad (i : Fin 3) : |g.cPsiGrad i| ≤ A * parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) :=
      (hG i x hx y hy hxy).trans (mul_le_mul_of_nonneg_right hGA (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
    have hs : |g.cPsiSq| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiSq :=
      (hB x hx y hy hxy).1.trans (mul_le_mul_of_nonneg_right hBA (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
    have hi0 : 0 < homogeneity κ .iPsiCube := by
      have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
      simp only [homogeneity]; linarith
    have hiγ : homogeneity κ .iPsiCube < gamma κ := by
      have hk0 : 0 < κ.1 := κ.2.1
      simp only [homogeneity, gamma]; linarith
    have hc : |g.cPsiCube| ≤ A * parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
      rw [show g.cPsiCube = _ from renormalisedGamma_cPsiCube_eq N κ noise R x y]
      exact (hE .iPsiCube hi0 hiγ x hx y hy hxy).trans
        (mul_le_mul_of_nonneg_right hEA (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
    change |structureGroupMap g (basis τ) σ| ≤ _
    rw [structureGroupMap_basis]
    exact gammaStructureBasis_weighted_bound κ g hdpos hA hshift hp hgrad hs hc τ σ

end RegularityStructures.Phi43

end
