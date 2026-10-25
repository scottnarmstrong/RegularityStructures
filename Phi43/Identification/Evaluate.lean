/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.CubeFull
public import Phi43.Identification.BaseFunctions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Evaluation at the base point

This is a step of the identification of the renormalised equation ([Hai14, p. 147]).

On the diagonal the base functions are
`Π^M_x Ψ (x) = ψ`, `Ψ² ↦ ψ² - C₁`, `Ψ³ ↦ ψ³ - 3C₁ψ`, `Ψ²Xᵢ ↦ 0`, `Ψ I(Ψ³) ↦ 0`,
`Ψ² I(Ψ²) ↦ -C₂`, `Ψ² I(Ψ³) ↦ -3C₂ψ`, `1 ↦ 1` (`phi43BaseFunctions_diag_*`), whence
`∑_τ (F(u) - Ξ)_τ (Π^M_x τ)(x) = -w³ + (3C₁ - 9C₂) w`, `w = ψ + φ`
(`phi43_evaluate_at_base`).
-/

public section

namespace RegularityStructures.Phi43

variable (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : RenormalisationConstants)
  (x : ParabolicSpace)

/-- The value `ψ(x) = (Π^M_x Ψ)(x)` of the stationary solution `K * ζ` at the base point. -/
noncomputable def phi43PsiAt : ℝ :=
  (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis .psi) x

private theorem diag_eq (τ : Symbol) (hτ : τ ∈ fMinus) :
    phi43BaseFunctions N κ noise C x τ x =
      (hairerCanonicalData (κ := κ) N noise).renormalisedBasedBasis C x τ x := by
  rw [phi43BaseFunctions_of_mem_fMinus N κ noise C hτ, renormalisedExtensionPi_basis_form]

private theorem psiAt_eq :
    phi43PsiAt N κ noise C x = (hairerCanonicalData (κ := κ) N noise).globalPsi x := by
  have h := diag_eq N κ noise C x .psi (by simp [mem_fMinus_iff_isFMinus, isFMinus])
  have h2 : phi43BaseFunctions N κ noise C x .psi x = phi43PsiAt N κ noise C x := by
    simp [phi43BaseFunctions, mem_fMinus_iff_isFMinus, isFMinus, phi43PsiAt]
  rw [← h2, h]
  simp [CanonicalData.renormalisedBasedBasis, CanonicalData.localPiBasis,
    CanonicalData.localPsi_eq_globalPsi]

theorem phi43BaseFunctions_diag_psi :
    phi43BaseFunctions N κ noise C x .psi x = phi43PsiAt N κ noise C x := by
  simp [phi43BaseFunctions, mem_fMinus_iff_isFMinus, isFMinus, phi43PsiAt]

theorem phi43BaseFunctions_diag_one : phi43BaseFunctions N κ noise C x .one x = 1 := by
  rw [phi43BaseFunctions_one]

private theorem globalPsiSq_eq :
    (hairerCanonicalData (κ := κ) N noise).globalPsiSq x = phi43PsiAt N κ noise C x ^ 2 := by
  rw [← CanonicalData.localPsiSq_eq_globalPsiSq, psiAt_eq, ← CanonicalData.localPsi_eq_globalPsi]
  simp [CanonicalData.localPsiSq, sq]

private theorem globalPsiCube_eq :
    (hairerCanonicalData (κ := κ) N noise).globalPsiCube x = phi43PsiAt N κ noise C x ^ 3 := by
  rw [← CanonicalData.localPsiCube_eq_globalPsiCube, psiAt_eq, ← CanonicalData.localPsi_eq_globalPsi]
  simp [CanonicalData.localPsiCube, CanonicalData.localPsiSq]
  ring

theorem phi43BaseFunctions_diag_psiSq :
    phi43BaseFunctions N κ noise C x .psiSq x = phi43PsiAt N κ noise C x ^ 2 - C₁ C := by
  rw [diag_eq N κ noise C x _ (by simp [mem_fMinus_iff_isFMinus, isFMinus])]
  simp [CanonicalData.renormalisedBasedBasis, globalPsiSq_eq N κ noise C x]

theorem phi43BaseFunctions_diag_psiCube :
    phi43BaseFunctions N κ noise C x .psiCube x =
      phi43PsiAt N κ noise C x ^ 3 - 3 * C₁ C * phi43PsiAt N κ noise C x := by
  rw [diag_eq N κ noise C x _ (by simp [mem_fMinus_iff_isFMinus, isFMinus])]
  simp [CanonicalData.renormalisedBasedBasis, globalPsiCube_eq N κ noise C x, psiAt_eq N κ noise C x]

theorem phi43BaseFunctions_diag_psiSqX (i : Fin 3) :
    phi43BaseFunctions N κ noise C x (.psiSqX i) x = 0 := by
  rw [diag_eq N κ noise C x _ (by simp [mem_fMinus_iff_isFMinus, isFMinus])]
  simp [CanonicalData.renormalisedBasedBasis, CanonicalData.relCoord]

private theorem based_cube_diag :
    (hairerCanonicalData (κ := κ) N noise).renormalisedBasedCube C x x = 0 := by
  have h := renormalisedExtensionPi_positive_at_base N κ noise C .iPsiCube
    (by have := κ.2.1; have := κ.2.2; simp only [homogeneity]; linarith) x
  rw [renormalisedExtensionPi_basis_form] at h
  simpa [CanonicalData.renormalisedBasedBasis] using h

private theorem localIPsiSq_diag :
    (hairerCanonicalData (κ := κ) N noise).localIPsiSq x x = 0 := by
  have h := canonicalPi_positive_at_base N κ noise .iPsiSq
    (by have := κ.2.1; have := κ.2.2; simp only [homogeneity]; linarith) x
  simpa [CanonicalData.canonicalPi_basis, CanonicalData.localPiBasis] using h

theorem phi43BaseFunctions_diag_iPsiCubePsi :
    phi43BaseFunctions N κ noise C x .iPsiCubePsi x = 0 := by
  rw [diag_eq N κ noise C x _ (by simp [mem_fMinus_iff_isFMinus, isFMinus])]
  simp [CanonicalData.renormalisedBasedBasis, based_cube_diag N κ noise C x]

theorem phi43BaseFunctions_diag_iPsiSqPsiSq :
    phi43BaseFunctions N κ noise C x .iPsiSqPsiSq x = -C₂ C := by
  rw [diag_eq N κ noise C x _ (by simp [mem_fMinus_iff_isFMinus, isFMinus])]
  simp [CanonicalData.renormalisedBasedBasis, localIPsiSq_diag N κ noise x]

theorem phi43BaseFunctions_diag_iPsiCubePsiSq :
    phi43BaseFunctions N κ noise C x .iPsiCubePsiSq x = -3 * C₂ C * phi43PsiAt N κ noise C x := by
  rw [diag_eq N κ noise C x _ (by simp [mem_fMinus_iff_isFMinus, isFMinus])]
  simp [CanonicalData.renormalisedBasedBasis, based_cube_diag N κ noise C x,
    psiAt_eq N κ noise C x]

/-- **Evaluation at the base point** ([Hai14, p. 147]): with `w = ψ(x) + φ`,
`∑_τ (F(u) - Ξ)_τ (Π^M_x τ)(x) = -w³ + (3C₁ - 9C₂) w`. -/
theorem phi43_evaluate_at_base (φ : ℝ) (ψ : Fin 3 → ℝ) :
    ∑ τ : Symbol, phi43FDisplayOld φ ψ τ * phi43BaseFunctions N κ noise C x τ x =
      -(phi43PsiAt N κ noise C x + φ) ^ 3 +
        (3 * C₁ C - 9 * C₂ C) * (phi43PsiAt N κ noise C x + φ) := by
  have hX : ∑ τ : Symbol, (∑ i, (3 * ψ i) • (Pi.single (Symbol.psiSqX i) 1 : Symbol → ℝ)) τ *
      phi43BaseFunctions N κ noise C x τ x = 0 := by
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, ite_mul, zero_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [phi43BaseFunctions_diag_psiSqX]
  simp only [phi43FDisplayOld, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, add_mul, sub_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, hX, Pi.single_apply, ite_mul, one_mul, zero_mul, mul_assoc]
  simp [Finset.sum_ite_eq', phi43BaseFunctions_diag_psi, phi43BaseFunctions_diag_one,
    phi43BaseFunctions_diag_psiSq, phi43BaseFunctions_diag_psiCube,
    phi43BaseFunctions_diag_iPsiCubePsi, phi43BaseFunctions_diag_iPsiSqPsiSq,
    phi43BaseFunctions_diag_iPsiCubePsiSq]
  ring

end RegularityStructures.Phi43

end
