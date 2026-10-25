/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionBasedForm
import Mathlib.Tactic.Ring
public import Phi43.Structure.CanonicalKernelHairer

/-!
# Source tensor agreement on Hairer's H0

The explicitly corrected smooth extension agrees with (Pi_x tensor f_x)
Delta^M on H0, together with I(Psi) and I(Psi^3). In particular this includes
every negative tree `F₋` required by the canonical-model predicate
`Statements.IsRenormalisedCanonicalModel`. The auxiliary positive square
`I(Psi^3)^2` is not claimed to agree with the corresponding row of the
algebraic tensor formula.

Source: Hairer [Hai14, (8.34), (9.3)–(9.5), Theorem 8.44].
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- The explicit smooth extension equals the source tensor formula on H0. -/
theorem renormalisedExtensionPi_eq_tensor_on_H0 (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (c : RenormalisationConstants) (x : ParabolicSpace)
    (τ : Symbol) (hτ : IsHairerF0 τ ∨ τ = .iPsi ∨ τ = .iPsiCube) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (basis τ) =
      (hairerCanonicalData (κ := κ) N noise).renormalisedPi c x (basis τ) := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
  have hp : 0 < κ.1 := κ.2.1
  have hI : 0 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have hI' : ¬ 1 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have hS : 0 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hS' : ¬ 1 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hJ : 0 < homogeneity κ .iPsi := by simp only [homogeneity]; linarith
  have hJ' : 1 < homogeneity κ .iPsi := by simp only [homogeneity]; linarith
  have hK (f : ParabolicSpace → ℝ) : D.kernel.convolutionOp f = D.kernel.taylorConstant f := rfl
  rw [renormalisedExtensionPi_basis_form]
  change D.renormalisedBasedBasis c x τ = D.renormalisedPi c x (basis τ)
  rw [CanonicalData.renormalisedPi_apply, deltaM_basis]
  cases τ <;> simp [IsHairerF0] at hτ
  all_goals
    simp only [deltaMBasis, map_add, map_smul, map_sum,
      CanonicalData.canonicalPiTensor_unit, CanonicalData.canonicalPiTensor_basis]
  all_goals
    simp only [M_basis, contraction_basis, L1BasisAction, L2BasisAction,
      map_sub, map_smul, map_zero, smul_zero, sub_zero, map_add,
      add_zero, sub_self, smul_smul, neg_smul, map_neg, smul_neg, neg_zero]
  all_goals funext y
  all_goals
    simp [CanonicalData.canonicalPi_basis, CanonicalData.localPiBasis,
      CanonicalData.renormalisedBasedBasis, CanonicalData.renormalisedBasedCube,
      CanonicalData.localIPsiCubePsi, CanonicalData.localIPsiCubePsiSq,
      CanonicalData.localIPsiPsiSq, CanonicalData.localIPsiPsi,
      CanonicalData.localIPsiSqPsiSq, CanonicalData.localIPsiSqPsi,
      CanonicalData.localPsiSqX, CanonicalData.localPsiX,
      CanonicalData.localPsi_eq_globalPsi, CanonicalData.localPsiSq_eq_globalPsiSq,
      CanonicalData.localPsiCube_eq_globalPsiCube, plusCharacter_basis, plusCharacterBasis,
      CanonicalData.canonicalCharacter, CanonicalData.canonicalCPsiGrad,
      CanonicalData.localIPsiCube, CanonicalData.localIPsiSq, CanonicalData.localIPsi,
      CanonicalData.globalIPsi, CanonicalData.integrate, CanonicalKernel.taylorPolynomial,
      hI, hI', hS, hS', hJ, hJ', CanonicalKernel.convolution, hK,
      CanonicalData.relCoord]
  all_goals try simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  all_goals ring

end RegularityStructures.Phi43

end
