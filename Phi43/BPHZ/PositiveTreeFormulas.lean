/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeFormulas
import Mathlib.Tactic
public import Phi43.Structure.CanonicalModel

/-!
# Explicit formulas for the renormalised lift on the positive-degree trees

For `D : CanonicalData κ`, constants `C = (C₁, C₂)` and a base point `z`, we compute
`D.renormalisedPi C z (basis τ)` for the non-polynomial symbols `τ` of positive homogeneity,
complementing `Phi43.BPHZ.TreeFormulas` (which treats `F₋`).  Writing `Ψ = D.localPsi` and
`⟦f⟧^r_z = D.integrate r f z`, with `r_τ` the homogeneity of the integrated symbol:

* `I(Ψ) ↦ ⟦Ψ⟧^{r_{I(Ψ)}}_z`, `ΨXᵢ ↦ Ψ (yᵢ - zᵢ)`, `I(Ψ²) ↦ ⟦Ψ²⟧^{r_{I(Ψ²)}}_z`
  (these are unchanged by `M` and by the coaction);
* `I(Ψ³) ↦ ⟦Ψ³⟧^{r}_z - 3 C₁ ⟦Ψ⟧^{r}_z` with `r = r_{I(Ψ³)} ≤ 1`: `M` changes `I(Ψ³)` to
  `I(Ψ³) - 3 C₁ I(Ψ)`, and the coaction correction `3 C₁ Σᵢ Xᵢ ⊗ J_i` exactly cancels the
  first-order Taylor term of `I(Ψ)`;
* `I(Ψ)Ψ ↦ ⟦Ψ⟧ Ψ`, `I(Ψ²)Ψ ↦ ⟦Ψ²⟧ Ψ`, `I(Ψ³)² ↦ (⟦Ψ³⟧)²` (unchanged by `M`);
* `I(Ψ)Ψ² ↦ ⟦Ψ⟧ (Ψ² - C₁)` (changed by `M`: `I(Ψ)Ψ² ↦ I(Ψ)Ψ² - C₁ I(Ψ)`).

`M` fixes `I(Ψ)`, `ΨXᵢ`, `I(Ψ²)`, `I(Ψ)Ψ`, `I(Ψ²)Ψ`, `I(Ψ³)²`, and changes exactly
`I(Ψ³)`, `I(Ψ)Ψ²` among the positive-degree symbols.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

namespace CanonicalData

local notation "E" => ParabolicSpace

variable {κ : Kappa} (D : CanonicalData κ)

theorem renormalisedPi_basis_iPsi_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .iPsi) =
      fun y => D.integrate (homogeneity κ .iPsi) D.localPsi z y := by
  rw [renormalisedPi_basis_of_deltaMBasis_eq D C z _ rfl]
  funext y
  simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction, localPiBasis, localIPsi]

theorem renormalisedPi_basis_iPsiSq_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .iPsiSq) =
      fun y => D.integrate (homogeneity κ .iPsiSq) D.localPsiSq z y := by
  rw [renormalisedPi_basis_of_deltaMBasis_eq D C z _ rfl]
  funext y
  simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction, localPiBasis, localIPsiSq]

private theorem posTree_iPsi_gt_one : 1 < homogeneity κ .iPsi := by
  have := κ.2.2
  simp only [homogeneity]; linarith

private theorem posTree_iPsiCube_pos : 0 < homogeneity κ .iPsiCube := by
  have := κ.2.2
  simp only [homogeneity]; linarith

private theorem posTree_iPsiCube_not_gt_one : ¬ 1 < homogeneity κ .iPsiCube := by
  have := κ.2.1
  simp only [homogeneity]; linarith

/-- `I(Ψ³) ↦ ⟦Ψ³⟧ - 3 C₁ ⟦Ψ⟧` (both at the order `r_{I(Ψ³)}`): the coaction correction
cancels the first-order Taylor term of `I(Ψ)`. -/
theorem renormalisedPi_basis_iPsiCube_eq (C : RenormalisationConstants) (z : E) :
    D.renormalisedPi C z (basis .iPsiCube) =
      fun y => D.integrate (homogeneity κ .iPsiCube) D.localPsiCube z y -
        3 * C₁ C * D.integrate (homogeneity κ .iPsiCube) D.localPsi z y := by
  rw [renormalisedPi_apply, deltaM_basis]
  simp only [deltaMBasis, map_add, map_smul, map_sum, canonicalPiTensor_tensorOf_one_eq,
    canonicalPiTensor_basis, canonicalCharacter_jPsiGrad, canonicalPi_basis]
  funext y
  have hM : M C (basis .iPsiCube) = basis .iPsiCube - (3 * C₁ C) • basis .iPsi := by
    simp [M_basis, contraction_basis, L1BasisAction, L2BasisAction, sub_eq_add_neg, smul_smul]
    rw [mul_comm]
  rw [hM]
  have hS : (∑ x : Fin 3, -D.kernel.taylorSpatial D.localPsi x z • D.localPiBasis z (.x x)) y
      = -(∑ i : Fin 3, D.kernel.taylorSpatial D.localPsi i z * relCoord z y i.succ) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, localPiBasis,
      ← Finset.sum_neg_distrib, neg_mul]
  rw [Pi.add_apply, Pi.smul_apply, hS, map_sub, map_smul]
  simp only [canonicalPi_basis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : D.localPiBasis z .iPsiCube y =
      D.integrate (homogeneity κ .iPsiCube) D.localPsiCube z y := rfl
  have h2 : D.localPiBasis z .iPsi y =
      D.integrate (homogeneity κ .iPsi) D.localPsi z y := rfl
  rw [h1, h2, integrate_eq_of_one_lt D posTree_iPsi_gt_one,
    integrate_eq_of_pos_of_not_gt_one D posTree_iPsiCube_pos posTree_iPsiCube_not_gt_one
      D.localPsi]
  ring

end CanonicalData

end RegularityStructures.Phi43

end
