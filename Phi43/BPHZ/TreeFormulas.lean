/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

import Mathlib.Tactic
public import Phi43.Structure.CanonicalModel

/-!
# Explicit formulas for the renormalised lift on the negative trees `F₋`

For `D : CanonicalData κ`, constants `C = (C₁, C₂)` and a base point `z`, we compute the
function `D.renormalisedPi C z (basis τ)` for the symbols `τ` of `Phi43.fMinus`, following
Hairer, arXiv:1303.5113v4, §10.5, (10.32)--(10.43).  Writing `Ψ = D.localPsi`, the results are

* `Ξ ↦ ζ`, `Ψ ↦ Ψ`, `Ψ² ↦ Ψ² - C₁`, `Ψ³ ↦ Ψ³ - 3 C₁ Ψ`,
  `Ψ² Xᵢ ↦ (Ψ² - C₁)(yᵢ - zᵢ)`;
* `I(Ψ³)Ψ ↦ Ψ · (⟦Ψ³⟧_z - 3 C₁ ⟦Ψ⟧_z)`;
* `I(Ψ²)Ψ² ↦ ⟦Ψ²⟧_z (Ψ² - C₁) - C₂`;
* `I(Ψ³)Ψ² ↦ (Ψ² - C₁)(⟦Ψ³⟧_z - 3 C₁ ⟦Ψ⟧_z) - 3 C₂ Ψ`,

where `⟦f⟧_z = D.integrate r f z` with `r` the homogeneity of the relevant integrated symbol.
The kernel record of `CanonicalData` is abstract (its convolution and Taylor functionals are not
assumed linear), so the integrals of the Hairer combinations `Ψ³ - 3 C₁ Ψ` and `Ψ² - C₁` are
written as the corresponding combinations of integrals rather than as `⟦Ψ³ - 3 C₁ Ψ⟧_z` and
`⟦Ψ² - C₁⟧_z`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

namespace CanonicalData

local notation "E" => ParabolicSpace

variable {κ : Kappa} (D : CanonicalData κ)

/-- The tensor realisation of `v ⊗ 1` is the based realisation of `v`. -/
theorem canonicalPiTensor_tensorOf_one_eq (z : E) (v : T) :
    D.canonicalPiTensor z (tensorOf v (plusBasis .one)) = D.canonicalPi z v := by
  have hlin : (D.canonicalPiTensor z).comp
      (Finsupp.bilinearCombination ℝ ℝ (fun τ : Symbol =>
        Finsupp.single τ (plusBasis .one))) = D.canonicalPi z := by
    apply Finsupp.lhom_ext
    intro σ r
    rw [← Finsupp.smul_single_one]
    simp only [LinearMap.comp_apply, map_smul]
    rw [show (Finsupp.bilinearCombination ℝ ℝ (fun σ : Symbol =>
        Finsupp.single σ (plusBasis .one))) (Finsupp.single σ 1) =
        tensorBasis σ .one by simp [tensorBasis, plusBasis]]
    rw [canonicalPiTensor_basis]
    have : plusCharacter (D.canonicalCharacter z) (plusBasis .one) = 1 := by
      simp [plusCharacter_basis, plusCharacterBasis]
    rw [this, one_smul]
    rfl
  exact LinearMap.congr_fun hlin _

/-- Core of `renormalisedPi` on a symbol whose coaction is the trivial one. -/
theorem renormalisedPi_basis_of_deltaMBasis_eq (C : RenormalisationConstants) (z : E)
    (τ : Symbol) (h : deltaMBasis C τ = tensorOf (M C (basis τ)) (plusBasis .one)) :
    D.renormalisedPi C z (basis τ) = D.canonicalPi z (M C (basis τ)) := by
  rw [renormalisedPi_apply, deltaM_basis, h, canonicalPiTensor_tensorOf_one_eq]

theorem renormalisedPi_basis_noise_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .noise) = D.noise.zeta := by
  rw [renormalisedPi_basis_of_deltaMBasis_eq D C z _ rfl]
  simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction]
  rfl

theorem renormalisedPi_basis_psi_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .psi) = D.localPsi := by
  rw [renormalisedPi_basis_of_deltaMBasis_eq D C z _ rfl]
  simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction]
  rfl

theorem renormalisedPi_basis_psiSq_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .psiSq) = fun y => D.localPsi y * D.localPsi y - C₁ C := by
  rw [renormalisedPi_basis_of_deltaMBasis_eq D C z _ rfl]
  funext y
  simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction, sub_eq_add_neg,
    localPiBasis, localPsiSq]

theorem renormalisedPi_basis_psiCube_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .psiCube) =
      fun y => D.localPsi y * D.localPsi y * D.localPsi y - 3 * C₁ C * D.localPsi y := by
  rw [renormalisedPi_basis_of_deltaMBasis_eq D C z _ rfl]
  funext y
  simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction, sub_eq_add_neg,
    localPiBasis, localPsiSq, localPsiCube]
  ring

theorem renormalisedPi_basis_psiSqX_eq (C : RenormalisationConstants) (z : E) (i : Fin 3) :
    D.renormalisedPi C z (basis (.psiSqX i)) =
      fun y => (D.localPsi y * D.localPsi y - C₁ C) * (relCoord z y i.succ) := by
  rw [renormalisedPi_basis_of_deltaMBasis_eq D C z _ rfl]
  funext y
  simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction, sub_eq_add_neg,
    localPiBasis, localPsiSqX, localPsiSq]
  ring

private theorem iPsi_gt_one : 1 < homogeneity κ .iPsi := by
  have := κ.2.2
  simp only [homogeneity]; linarith

private theorem iPsiCube_pos : 0 < homogeneity κ .iPsiCube := by
  have := κ.2.2
  simp only [homogeneity]; linarith

private theorem iPsiCube_not_gt_one : ¬ 1 < homogeneity κ .iPsiCube := by
  have := κ.2.1
  simp only [homogeneity]; linarith

/-- Taylor-subtracted integration at a constant-order homogeneity (`0 < r ≤ 1`). -/
theorem integrate_eq_of_pos_of_not_gt_one {r : ℝ} (h0 : 0 < r) (h1 : ¬ 1 < r)
    (f : E → ℝ) (z y : E) :
    D.integrate r f z y =
      CanonicalKernel.convolution D.kernel f y - D.kernel.taylorConstant f z := by
  simp [integrate, CanonicalKernel.taylorPolynomial, h0, h1]

/-- Taylor-subtracted integration at a homogeneity above one. -/
theorem integrate_eq_of_one_lt {r : ℝ} (h1 : 1 < r) (f : E → ℝ) (z y : E) :
    D.integrate r f z y =
      CanonicalKernel.convolution D.kernel f y - D.kernel.taylorConstant f z -
        ∑ i : Fin 3, D.kernel.taylorSpatial f i z * relCoord z y i.succ := by
  have h0 : 0 < r := by linarith
  simp [integrate, CanonicalKernel.taylorPolynomial, h0, h1, relCoord, sub_eq_add_neg,
    add_assoc]
  ring

theorem renormalisedPi_basis_iPsiCubePsi_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .iPsiCubePsi) =
      fun y => D.localPsi y *
        (D.integrate (homogeneity κ .iPsiCube) (D.localPsiCube) z y -
          3 * C₁ C * D.integrate (homogeneity κ .iPsiCube) D.localPsi z y) := by
  rw [renormalisedPi_apply, deltaM_basis]
  simp only [deltaMBasis, map_add, map_smul, map_sum, canonicalPiTensor_tensorOf_one_eq,
    canonicalPiTensor_basis, canonicalCharacter_jPsiGrad, canonicalPi_basis]
  funext y
  have hM : M C (basis .iPsiCubePsi) = basis .iPsiCubePsi - (3 * C₁ C) • basis .iPsiPsi := by
    simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction, sub_eq_add_neg, smul_smul]
    rw [mul_comm]
  rw [hM]
  have hI : D.localIPsi z y = D.integrate (homogeneity κ .iPsi) D.localPsi z y := rfl
  have hS : (∑ x : Fin 3, -D.kernel.taylorSpatial D.localPsi x z • D.localPiBasis z (.psiX x)) y
      = -(D.localPsi y * ∑ i : Fin 3, D.kernel.taylorSpatial D.localPsi i z *
          relCoord z y i.succ) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, localPiBasis, localPsiX,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Pi.add_apply, Pi.smul_apply, hS, map_sub, map_smul]
  simp only [canonicalPi_basis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : D.localPiBasis z .iPsiCubePsi y =
      D.integrate (homogeneity κ .iPsiCube) D.localPsiCube z y * D.localPsi y := rfl
  have h2 : D.localPiBasis z .iPsiPsi y =
      D.integrate (homogeneity κ .iPsi) D.localPsi z y * D.localPsi y := rfl
  rw [h1, h2, integrate_eq_of_one_lt D iPsi_gt_one,
    integrate_eq_of_pos_of_not_gt_one D iPsiCube_pos iPsiCube_not_gt_one D.localPsi]
  ring

theorem renormalisedPi_basis_iPsiSqPsiSq_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .iPsiSqPsiSq) =
      fun y => D.integrate (homogeneity κ .iPsiSq) D.localPsiSq z y *
        (D.localPsi y * D.localPsi y - C₁ C) - C₂ C := by
  rw [renormalisedPi_basis_of_deltaMBasis_eq D C z _ rfl]
  have hM : M C (basis .iPsiSqPsiSq) =
      basis .iPsiSqPsiSq - C₁ C • basis .iPsiSq - C₂ C • basis .one := by
    simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction, sub_eq_add_neg, add_assoc]
  rw [hM]
  funext y
  simp only [map_sub, map_smul, canonicalPi_basis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : D.localPiBasis z .iPsiSqPsiSq y =
      D.integrate (homogeneity κ .iPsiSq) D.localPsiSq z y * D.localPsiSq y := rfl
  have h2 : D.localPiBasis z .iPsiSq y =
      D.integrate (homogeneity κ .iPsiSq) D.localPsiSq z y := rfl
  have h3 : D.localPiBasis z .one y = 1 := rfl
  rw [h1, h2, h3]
  simp only [localPsiSq]
  ring

theorem renormalisedPi_basis_iPsiCubePsiSq_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .iPsiCubePsiSq) =
      fun y => (D.localPsi y * D.localPsi y - C₁ C) *
        (D.integrate (homogeneity κ .iPsiCube) D.localPsiCube z y -
          3 * C₁ C * D.integrate (homogeneity κ .iPsiCube) D.localPsi z y) -
        3 * C₂ C * D.localPsi y := by
  rw [renormalisedPi_apply, deltaM_basis]
  simp only [deltaMBasis, map_add, map_smul, map_sum, canonicalPiTensor_tensorOf_one_eq,
    canonicalPiTensor_basis, canonicalCharacter_jPsiGrad, canonicalPi_basis]
  funext y
  have hM : M C (basis .iPsiCubePsiSq) = basis .iPsiCubePsiSq - C₁ C • basis .iPsiCube -
      (3 * C₁ C) • basis .iPsiPsiSq - (3 * C₂ C) • basis .psi +
      (3 * C₁ C * C₁ C) • basis .iPsi := by
    simp [M_basis, L1BasisAction, L2BasisAction, contraction]
    module
  rw [hM]
  have hS2 : (∑ x : Fin 3, -D.kernel.taylorSpatial D.localPsi x z •
      D.localPiBasis z (.psiSqX x)) y =
      -(D.localPsi y * D.localPsi y * ∑ i : Fin 3, D.kernel.taylorSpatial D.localPsi i z *
          relCoord z y i.succ) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, localPiBasis, localPsiSqX,
      localPsiSq, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hS3 : (∑ x : Fin 3, -D.kernel.taylorSpatial D.localPsi x z •
      D.localPiBasis z (.x x)) y =
      -(∑ i : Fin 3, D.kernel.taylorSpatial D.localPsi i z * relCoord z y i.succ) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, localPiBasis,
      ← Finset.sum_neg_distrib, neg_mul]
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hS2, hS3]
  simp only [map_add, map_sub, map_smul, canonicalPi_basis, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  have h1 : D.localPiBasis z .iPsiCubePsiSq y =
      D.integrate (homogeneity κ .iPsiCube) D.localPsiCube z y * D.localPsiSq y := rfl
  have h2 : D.localPiBasis z .iPsiCube y =
      D.integrate (homogeneity κ .iPsiCube) D.localPsiCube z y := rfl
  have h3 : D.localPiBasis z .iPsiPsiSq y =
      D.integrate (homogeneity κ .iPsi) D.localPsi z y * D.localPsiSq y := rfl
  have h4 : D.localPiBasis z .iPsi y =
      D.integrate (homogeneity κ .iPsi) D.localPsi z y := rfl
  have h5 : D.localPiBasis z .psi y = D.localPsi y := rfl
  rw [h1, h2, h3, h4, h5, integrate_eq_of_one_lt D iPsi_gt_one,
    integrate_eq_of_pos_of_not_gt_one D iPsiCube_pos iPsiCube_not_gt_one D.localPsi]
  simp only [localPsiSq]
  ring

end CanonicalData

end RegularityStructures.Phi43

end
