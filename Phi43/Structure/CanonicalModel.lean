/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalModelData
public import Phi43.Structure.AbstractIntegration
public import Phi43.Structure.HairerCompatibility
import Mathlib.Tactic

/-!
# The fixed-regularisation canonical model

This module gives the algebraic canonical lift from Hairer [Hai14, §8.2, (8.18)--(8.26)] for the
finite Φ⁴₃ sector.  The data in `CanonicalData` contain a smooth periodic noise and abstract
translation-invariant convolution and Taylor-coefficient operations.  The function-valued lift
is defined recursively in `CanonicalModelData`; here it is related to Hairer's characters `f_z`,
and hence to the structure-group maps `Γ_{zz'}`.

No analytic model bounds are asserted here.  A later kernel-analysis module can identify the
abstract operations with the truncated heat kernel and then transport this algebraic lift to an
analytic model.

Source: Hairer, arXiv:1303.5113v4, §8.2, equations (8.18)--(8.26), §8.3, and §9.2.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators

namespace RegularityStructures.Phi43

open RegularityStructures

namespace CanonicalData

local notation "E" => ParabolicSpace

variable {κ : Kappa} (D : CanonicalData κ)

/-! ### Hairer's character `f_z` -/

def canonicalShift (z : E) : Fin 4 → ℝ := fun i => -parabolicCoords z i

def canonicalCPsiGrad (z : E) (i : Fin 3) : ℝ :=
  -D.kernel.taylorSpatial (localPsi D) i z

def canonicalCPsi (z : E) : ℝ :=
  -D.kernel.taylorConstant (localPsi D) z +
    ∑ i : Fin 3, canonicalShift z i.succ * canonicalCPsiGrad D z i

def canonicalCharacter (z : E) : G where
  shift := canonicalShift z
  cPsi := canonicalCPsi D z
  cPsiGrad := canonicalCPsiGrad D z
  cPsiSq := -D.kernel.taylorConstant (localPsiSq D) z
  cPsiCube := -D.kernel.taylorConstant (localPsiCube D) z

@[simp]
theorem canonicalCharacter_shift (z : E) :
    (D.canonicalCharacter z).shift = canonicalShift z := rfl

theorem canonicalCharacter_jPsiGrad (z : E) (i : Fin 3) :
    plusCharacter (D.canonicalCharacter z) (plusBasis (.jPsiGrad i)) =
      -D.kernel.taylorSpatial (localPsi D) i z := by
  simp [plusCharacter_basis, plusCharacterBasis, canonicalCharacter,
    canonicalCPsiGrad]

theorem localPsi_eq_globalPsi : localPsi D = globalPsi D := by
  funext y
  unfold localPsi integrate globalPsi
  have hκ : homogeneity κ .psi ≤ 0 := by
    simp [homogeneity]
    linarith [kappa_pos κ]
  rw [CanonicalKernel.taylorPolynomial_of_nonpos D.kernel hκ]
  simp [CanonicalKernel.convolution]

theorem localPsiSq_eq_globalPsiSq : localPsiSq D = globalPsiSq D := by
  funext y
  simp [localPsiSq, globalPsiSq, localPsi_eq_globalPsi D]

theorem localPsiCube_eq_globalPsiCube : localPsiCube D = globalPsiCube D := by
  funext y
  simp [localPsiCube, globalPsiCube, localPsiSq_eq_globalPsiSq D,
    localPsi_eq_globalPsi D]

/-! ### The parameter and group map `Γ_{zz'}` -/

def canonicalGammaParameter (z z' : E) : G :=
  structureGroupInv (D.canonicalCharacter z) * D.canonicalCharacter z'

def canonicalGamma (z z' : E) : T →ₗ[ℝ] T :=
  structureGroupMap (D.canonicalGammaParameter z z')

theorem structureGroupMul_assoc (a b c : G) :
    (a * b) * c = a * (b * c) := by
  cases a with
  | mk aShift aPsi aGrad aSq aCube =>
    cases b with
    | mk bShift bPsi bGrad bSq bCube =>
      cases c with
      | mk cShift cPsi cGrad cSq cCube =>
        change
          (⟨(aShift + bShift) + cShift,
            (aPsi + bPsi + ∑ i : Fin 3, aShift i.succ * bGrad i) + cPsi +
              ∑ i : Fin 3, (aShift + bShift) i.succ * cGrad i,
            (aGrad + bGrad) + cGrad, (aSq + bSq) + cSq,
            (aCube + bCube) + cCube⟩ : G) =
          (⟨aShift + (bShift + cShift),
            aPsi + (bPsi + cPsi + ∑ i : Fin 3, bShift i.succ * cGrad i) +
              ∑ i : Fin 3, aShift i.succ * (bGrad + cGrad) i,
            aGrad + (bGrad + cGrad), aSq + (bSq + cSq),
            aCube + (bCube + cCube)⟩ : G)
        congr 1
        · funext i
          change aShift i + bShift i + cShift i = aShift i + (bShift i + cShift i)
          abel
        · simp only [Pi.add_apply, Finset.sum_add_distrib, add_mul, mul_add]
          ring
        · funext i
          change aGrad i + bGrad i + cGrad i = aGrad i + (bGrad i + cGrad i)
          abel
        · abel
        · abel

theorem structureGroup_zero_mul (g : G) : 0 * g = g := by
  cases g with
  | mk shift cPsi cPsiGrad cPsiSq cPsiCube =>
    change
      (⟨0 + shift,
        0 + cPsi + ∑ i : Fin 3, 0 * cPsiGrad i,
        0 + cPsiGrad, 0 + cPsiSq, 0 + cPsiCube⟩ : G) = _
    congr
    · funext i
      simp
    · simp
    · funext i
      simp
    · simp
    · simp

theorem structureGroupMul_right_inv (g : G) :
    g * structureGroupInv g = 0 := by
  cases g with
  | mk shift cPsi cPsiGrad cPsiSq cPsiCube =>
    change
      (⟨shift + -shift,
        cPsi + (-cPsi + ∑ i : Fin 3, shift i.succ * cPsiGrad i) +
          ∑ i : Fin 3, shift i.succ * (-cPsiGrad i),
        cPsiGrad + -cPsiGrad, cPsiSq + -cPsiSq,
        cPsiCube + -cPsiCube⟩ : G) = (0 : G)
    congr
    · funext i
      change shift i + -shift i = 0
      simp
    · simp only [Finset.sum_neg_distrib, mul_neg]
      ring
    · funext i
      change cPsiGrad i + -cPsiGrad i = 0
      simp
    · simp
    · simp

/-! ### Recursive lift and the character bridge -/

def canonicalPi (z : E) : T →ₗ[ℝ] (E → ℝ) := D.localPi z

@[simp]
theorem canonicalPi_basis (z : E) (τ : Symbol) :
    D.canonicalPi z (basis τ) = D.localPiBasis z τ := by
  exact D.localPi_basis z τ

theorem canonicalPi_one (z : E) : D.canonicalPi z (basis .one) = fun _ => 1 := by
  rw [canonicalPi_basis]
  rfl

theorem canonicalPi_noise (z : E) : D.canonicalPi z (basis .noise) = D.noise.zeta := by
  rw [canonicalPi_basis]
  rfl

theorem canonicalPi_x (z : E) (i : Fin 3) :
    D.canonicalPi z (basis (.x i)) = fun y => relCoord z y i.succ := by
  rw [canonicalPi_basis]
  rfl

theorem canonicalPi_integration (z : E) :
    D.canonicalPi z (basis .iPsi) = fun y =>
      CanonicalKernel.convolution D.kernel (D.canonicalPi z (basis .psi)) y -
        D.kernel.taylorPolynomial (homogeneity κ .iPsi)
          (D.canonicalPi z (basis .psi)) z y := by
  funext y
  rw [canonicalPi_basis, canonicalPi_basis]
  rfl

private theorem parabolicCoords_sub (y z : E) (i : Fin 4) :
    parabolicCoords (y - z) i = parabolicCoords y i - parabolicCoords z i := by
  fin_cases i <;> simp [parabolicCoords]

private theorem iPsi_homogeneity_pos : 0 < homogeneity κ .iPsi := by
  simp [homogeneity]
  have hk : κ.1 < 1 / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
  linarith

private theorem iPsi_homogeneity_gt_one : 1 < homogeneity κ .iPsi := by
  simp [homogeneity]
  have hk : κ.1 < 1 / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
  linarith

private theorem iPsiSq_homogeneity_pos : 0 < homogeneity κ .iPsiSq := by
  simp [homogeneity]
  have hk : κ.1 < 1 / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
  linarith

private theorem iPsiSq_homogeneity_not_gt_one : ¬ 1 < homogeneity κ .iPsiSq := by
  simp [homogeneity]
  linarith [kappa_pos κ]

private theorem iPsiCube_homogeneity_pos : 0 < homogeneity κ .iPsiCube := by
  simp [homogeneity]
  have hk : κ.1 < 1 / 16 := by simpa [kappa₀] using kappa_lt_kappa₀ κ
  linarith

private theorem iPsiCube_homogeneity_not_gt_one : ¬ 1 < homogeneity κ .iPsiCube := by
  simp [homogeneity]
  linarith [kappa_pos κ]

private theorem sum_mul_fintype (f : Fin 3 → ℝ) (a : ℝ) :
    (∑ i, f i) * a = ∑ i, f i * a := by
  rw [Finset.sum_mul]

private theorem integrated_bridge (a c : ℝ) (f g h : Fin 3 → ℝ) :
    a - (c + ∑ i, f i * (g i - h i)) =
      a + (-c + ∑ i, h i * f i) + -∑ i, f i * g i := by
  have hsum : (∑ i, f i * (g i - h i)) =
      (∑ i, f i * g i) - ∑ i, f i * h i := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hfh : (∑ i, f i * h i) = ∑ i, h i * f i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, hfh]
  ring

private theorem integrated_bridge_mul (a c q : ℝ) (f g h : Fin 3 → ℝ) :
    (a - (c + ∑ i, f i * (g i - h i))) * q =
      a * q + (-c + ∑ i, h i * f i) * q +
        -∑ i, f i * (q * g i) := by
  have hsum : (∑ i, f i * (g i - h i)) =
      (∑ i, f i * g i) - ∑ i, f i * h i := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hfg : (∑ i, f i * g i) * q = ∑ i, f i * (q * g i) := by
    rw [sum_mul_fintype]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hfh : (∑ i, f i * h i) * q = (∑ i, h i * f i) * q := by
    apply congrArg (fun r : ℝ => r * q)
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  calc
    (a - (c + ((∑ i, f i * g i) - ∑ i, f i * h i))) * q =
        a * q - c * q - (∑ i, f i * g i) * q +
          (∑ i, f i * h i) * q := by ring
    _ = a * q + (-c + ∑ i, h i * f i) * q +
          -∑ i, f i * (q * g i) := by
      rw [hfg, hfh]
      ring

set_option linter.unusedSimpArgs false in
theorem canonicalPi_character_bridge_basis (z : E) (τ : Symbol) :
    D.canonicalPi z (basis τ) =
      D.globalPi (structureGroupMap (D.canonicalCharacter z) (basis τ)) := by
  rw [canonicalPi_basis, structureGroupMap_basis]
  cases τ
  case xMul p =>
    induction p using Sym2.inductionOn with
    | _ i j =>
        funext y
        simp [structureBasisAction, primitiveAction, xMulAction, globalPi_basis,
          globalPiBasis, multiply_basis, basisProduct, productSymbol,
          globalPolynomialQuadratic, localPolynomialQuadratic, canonicalShift,
          localPiBasis, relCoord, parabolicCoords_sub]
        ring
  all_goals
    simp [structureBasisAction, primitiveAction, integratedPsiProductAction,
      xMulAction, globalPi_basis, globalPiBasis, localPiBasis,
      localPolynomialQuadratic, globalPolynomialQuadratic, multiply_basis,
      basisProduct, productSymbol, canonicalCharacter, canonicalCPsi,
      canonicalCPsiGrad, localPsi_eq_globalPsi, localPsiSq_eq_globalPsiSq,
      localPsiCube_eq_globalPsiCube, localIPsi, localIPsiSq, localIPsiCube,
      localIPsiPsi, localIPsiPsiSq, localIPsiSqPsi, localIPsiSqPsiSq,
      localIPsiCubePsi, localIPsiCubePsiSq, localIPsiCubeSq, globalPsi,
      globalPsiSq, globalPsiCube, globalIPsi, globalIPsiSq, globalIPsiCube,
      globalIPsiPsi, globalIPsiPsiSq, globalIPsiSqPsi, globalIPsiSqPsiSq,
      globalIPsiCubePsi, globalIPsiCubePsiSq, globalIPsiCubeSq, integrate,
      CanonicalKernel.taylorPolynomial, relCoord,
      globalPsiX, globalPsiSqX, localPsiX, localPsiSqX, canonicalShift,
      iPsi_homogeneity_pos, iPsi_homogeneity_gt_one,
      iPsiSq_homogeneity_pos, iPsiSq_homogeneity_not_gt_one,
      iPsiCube_homogeneity_pos, iPsiCube_homogeneity_not_gt_one]
  all_goals try funext y
  all_goals
    simp [structureBasisAction, primitiveAction, integratedPsiProductAction,
      xMulAction, globalPi_basis, globalPiBasis, localPiBasis,
      localPolynomialQuadratic, globalPolynomialQuadratic, multiply_basis,
      basisProduct, productSymbol, canonicalCharacter, canonicalCPsi,
      canonicalCPsiGrad, localPsi_eq_globalPsi, localPsiSq_eq_globalPsiSq,
      localPsiCube_eq_globalPsiCube, localIPsi, localIPsiSq, localIPsiCube,
      localIPsiPsi, localIPsiPsiSq, localIPsiSqPsi, localIPsiSqPsiSq,
      localIPsiCubePsi, localIPsiCubePsiSq, localIPsiCubeSq, globalPsi,
      globalPsiSq, globalPsiCube, globalIPsi, globalIPsiSq, globalIPsiCube,
      globalIPsiPsi, globalIPsiPsiSq, globalIPsiSqPsi, globalIPsiSqPsiSq,
      globalIPsiCubePsi, globalIPsiCubePsiSq, globalIPsiCubeSq, integrate,
      CanonicalKernel.taylorPolynomial, relCoord, parabolicCoords_sub,
      globalPsiX, globalPsiSqX, localPsiX, localPsiSqX, canonicalShift,
      iPsi_homogeneity_pos, iPsi_homogeneity_gt_one,
      iPsiSq_homogeneity_pos, iPsiSq_homogeneity_not_gt_one,
      iPsiCube_homogeneity_pos, iPsiCube_homogeneity_not_gt_one]
  case iPsi =>
    apply integrated_bridge
  case iPsiPsi =>
    apply integrated_bridge_mul
  case iPsiPsiSq =>
    apply integrated_bridge_mul
  all_goals ring

theorem canonicalPi_character_bridge (z : E) :
    D.canonicalPi z =
      (D.globalPi.comp (structureGroupMap (D.canonicalCharacter z))) := by
  apply Finsupp.lhom_ext
  intro τ r
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  change r • D.canonicalPi z (basis τ) =
    r • D.globalPi (structureGroupMap (D.canonicalCharacter z) (basis τ))
  rw [D.canonicalPi_character_bridge_basis]

theorem canonicalPi_gamma_basis (z z' : E) (τ : Symbol) :
    D.canonicalPi z (D.canonicalGamma z z' (basis τ)) =
      D.canonicalPi z' (basis τ) := by
  rw [canonicalPi_character_bridge, canonicalPi_character_bridge]
  change D.globalPi
      ((structureGroupMap (D.canonicalCharacter z)).comp
        (structureGroupMap (D.canonicalGammaParameter z z')) (basis τ)) =
    D.globalPi (structureGroupMap (D.canonicalCharacter z') (basis τ))
  rw [structureGroupMap_comp]
  congr 1
  unfold canonicalGammaParameter
  rw [← structureGroupMul_assoc, structureGroupMul_right_inv,
    structureGroup_zero_mul]

theorem canonicalPi_gamma (z z' : E) (v : T) :
    D.canonicalPi z (D.canonicalGamma z z' v) = D.canonicalPi z' v := by
  have hcomp :
      (D.canonicalPi z).comp (D.canonicalGamma z z') = D.canonicalPi z' := by
    apply Finsupp.lhom_ext
    intro τ r
    rw [← Finsupp.smul_single_one, map_smul, map_smul]
    change r • D.canonicalPi z (D.canonicalGamma z z' (basis τ)) =
      r • D.canonicalPi z' (basis τ)
    rw [canonicalPi_gamma_basis]
  exact LinearMap.congr_fun hcomp v

/-! ### The renormalised canonical lift -/

/- The tensor expression `(Π_z ⊗ f_z) Δᴹ` from Hairer (8.34). -/
def canonicalPiTensor (z : E) : Tensor →ₗ[ℝ] (E → ℝ) :=
  (D.canonicalPi z).comp (deltaCharacterLinear (D.canonicalCharacter z))

private theorem canonicalPiTensor_tensorOf_one (z : E) (v : T) :
    D.canonicalPiTensor z (tensorOf v (plusBasis .one)) = D.canonicalPi z v := by
  have hlin : (D.canonicalPiTensor z).comp
      (Finsupp.bilinearCombination ℝ ℝ (fun τ : Symbol =>
        Finsupp.single τ (plusBasis .one))) = D.canonicalPi z := by
    apply Finsupp.lhom_ext
    intro τ r
    rw [← Finsupp.smul_single_one]
    simp only [LinearMap.comp_apply, map_smul]
    rw [show (Finsupp.bilinearCombination ℝ ℝ (fun σ : Symbol =>
        Finsupp.single σ (plusBasis .one))) (Finsupp.single τ 1) =
        tensorBasis τ .one by simp [tensorBasis, plusBasis]]
    rw [canonicalPiTensor, LinearMap.comp_apply]
    change r • D.canonicalPi z
        (deltaCharacter (D.canonicalCharacter z) (tensorBasis τ .one)) = _
    rw [deltaCharacter_tensorBasis, map_smul]
    simp [plusCharacter, plusCharacterBasis, plusBasis, basis]
  exact LinearMap.congr_fun hlin v

theorem canonicalPiTensor_basis (z : E) (τ : Symbol) (p : PlusSymbol) :
    D.canonicalPiTensor z (tensorBasis τ p) =
      (plusCharacter (D.canonicalCharacter z) (plusBasis p)) •
        D.canonicalPi z (basis τ) := by
  rw [canonicalPiTensor, LinearMap.comp_apply]
  change D.canonicalPi z
      (deltaCharacter (D.canonicalCharacter z) (tensorBasis τ p)) = _
  rw [deltaCharacter_tensorBasis]
  rw [map_smul]

private theorem canonicalPi_x_at_base (z : E) (i : Fin 3) :
    D.canonicalPi z (basis (.x i)) z = 0 := by
  rw [canonicalPi_x]
  simp [relCoord, parabolicCoords]

private theorem canonicalPi_psiX_at_base (z : E) (i : Fin 3) :
    D.canonicalPi z (basis (.psiX i)) z = 0 := by
  rw [canonicalPi_basis]
  simp [localPiBasis, localPsiX, relCoord, parabolicCoords]

private theorem canonicalPi_psiSqX_at_base (z : E) (i : Fin 3) :
    D.canonicalPi z (basis (.psiSqX i)) z = 0 := by
  rw [canonicalPi_basis]
  simp [localPiBasis, localPsiSqX, relCoord, parabolicCoords]

private theorem canonicalPiTensor_psiX_at_base (z : E) (i : Fin 3) :
    D.canonicalPiTensor z (tensorBasis (.psiX i) (.jPsiGrad i)) z = 0 := by
  rw [canonicalPiTensor_basis]
  simp only [Pi.smul_apply]
  rw [canonicalPi_psiX_at_base]
  simp

private theorem canonicalPiTensor_psiSqX_at_base (z : E) (i : Fin 3) :
    D.canonicalPiTensor z (tensorBasis (.psiSqX i) (.jPsiGrad i)) z = 0 := by
  rw [canonicalPiTensor_basis]
  simp only [Pi.smul_apply]
  rw [canonicalPi_psiSqX_at_base]
  simp

private theorem canonicalPiTensor_x_at_base (z : E) (i : Fin 3) :
    D.canonicalPiTensor z (tensorBasis (.x i) (.jPsiGrad i)) z = 0 := by
  rw [canonicalPiTensor_basis]
  simp only [Pi.smul_apply]
  rw [canonicalPi_x_at_base]
  simp

/-- Hairer's renormalised realisation, defined by the tensor formula (8.34). -/
def renormalisedPi (C : RenormalisationConstants) (z : E) :
    T →ₗ[ℝ] (E → ℝ) := (D.canonicalPiTensor z).comp (deltaM C)

theorem renormalisedPi_apply (C : RenormalisationConstants) (z : E) (v : T) :
    D.renormalisedPi C z v =
      D.canonicalPiTensor z (deltaM C v) := rfl

theorem renormalisedPi_basis_at_base (C : RenormalisationConstants) (z : E) (τ : Symbol) :
    D.renormalisedPi C z (basis τ) z = D.canonicalPi z (M C (basis τ)) z := by
  rw [renormalisedPi, LinearMap.comp_apply, deltaM_basis]
  cases τ <;>
    simp [deltaMBasis, canonicalPiTensor_tensorOf_one]
  case iPsiCube =>
    right
    apply Finset.sum_eq_zero
    intro i hi
    exact canonicalPiTensor_x_at_base D z i
  case iPsiCubePsi =>
    right
    apply Finset.sum_eq_zero
    intro i hi
    simpa [tensorBasis] using canonicalPiTensor_psiX_at_base D z i
  case iPsiCubePsiSq =>
    have hzero₁ : (∑ i, D.canonicalPiTensor z
        (tensorBasis (.psiSqX i) (.jPsiGrad i)) z) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact canonicalPiTensor_psiSqX_at_base D z i
    have hzero₂ : (∑ i, D.canonicalPiTensor z
        (tensorBasis (.x i) (.jPsiGrad i)) z) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact canonicalPiTensor_x_at_base D z i
    rw [hzero₁, hzero₂]
    simp

theorem renormalisedPi_at_base (C : RenormalisationConstants) (z : E) (v : T) :
    D.renormalisedPi C z v z = D.canonicalPi z (M C v) z := by
  let evalZ : (E → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => f z
      map_add' := fun f g => rfl
      map_smul' := fun r f => rfl }
  have hlin : (evalZ.comp (D.renormalisedPi C z)) =
      evalZ.comp ((D.canonicalPi z).comp (M C)) := by
    apply Finsupp.lhom_ext
    intro τ r
    rw [← Finsupp.smul_single_one, map_smul, map_smul]
    change r • D.renormalisedPi C z (basis τ) z =
      r • D.canonicalPi z (M C (basis τ)) z
    rw [renormalisedPi_basis_at_base]
  exact LinearMap.congr_fun hlin v

/-! ### The renormalised structure group -/

/- The map in Hairer (8.41), with `∆̂ᴹ` as defined in (8.38). -/

end CanonicalData

end RegularityStructures.Phi43

end
