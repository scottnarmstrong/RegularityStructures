/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentField
public import Phi43.BPHZ.CanonicalBridgeHairer
public import Phi43.BPHZ.GammaFullKernels
public import Phi43.BPHZ.GammaFullGrad
public import Phi43.BPHZ.GammaMomentGradBridgeIncrements
import Mathlib.Tactic

/-!
# Explicit rows of the extension `Π` of the canonical model, for arbitrary constants

For a smooth noise `ξ ω` and arbitrary constants `C`, the extension `Π_x τ` of the canonical model
of the lift of `ξ ω` is an explicit function of `y` on the `F₋` symbols and the positive-degree
symbols, in particular for the shifted constants. This file collects these rows in one place,
`shiftedPi_row_*`, together with the decomposition of the kernel-increment pairing of `Ψ` into the
recentred part and the spatial gradient at the base point (`shiftedPi_pairing_psi_eq`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  (C : RenormalisationConstants) (x : ParabolicSpace)

local notation "Ext" => CanonicalData.renormalisedExtensionPi

private theorem shiftedPi_isHairerF0_of_isFMinus {τ : Symbol} (hτ : isFMinus τ) :
    IsHairerF0 τ := by
  cases τ <;> simp_all [isFMinus, IsHairerF0]

/-- The `F₋` rows of the extension (all symbols but `Ψ²Xᵢ`) are the pathwise tree fields. -/
theorem shiftedPi_row_treeField (hf : IsSmoothOnSpaceTime (ξ ω)) {τ : Symbol}
    (hτ : isFMinus τ) (hX : ∀ i, τ ≠ .psiSqX i) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis τ) =
      fun y => hairerTreeField N ξ (C₁ C) (C₂ C) (spaceTimeProj x) ω τ (spaceTimeProj y) := by
  rw [renormalisedExtensionPi_eq_tensor_on_H0 N κ _ C x τ
    (Or.inl (shiftedPi_isHairerF0_of_isFMinus hτ))]
  exact CanonicalData.hairerCanonicalData_renormalisedPi_basis_eq_treeField C x (fun _ => rfl) hf
    ((mem_fMinus_iff_isFMinus τ).2 hτ) hX

theorem shiftedPi_row_psiSqX (hf : IsSmoothOnSpaceTime (ξ ω)) (i : Fin 3) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis (.psiSqX i)) =
      fun y => hairerTreePsiSq N ξ (C₁ C) ω (spaceTimeProj y) * (y.2 i - x.2 i) := by
  rw [renormalisedExtensionPi_eq_tensor_on_H0 N κ _ C x (.psiSqX i) (Or.inl trivial)]
  exact CanonicalData.hairerCanonicalData_renormalisedPi_basis_psiSqX_eq x C (fun _ => rfl) hf i


/-- The spatial gradient `∂ₖ(K ∗ Ψ)(x)` at the base point. -/
@[expose] noncomputable def shiftedPiGrad (N : ℕ) {Ω : Type*} (ξ : Ω → SpaceTime → ℝ) (ω : Ω)
    (x : ParabolicSpace) (k : Fin 3) : ℝ :=
  gammaFullGrad N ξ k (spaceTimeProj x) ω

theorem shiftedPi_pairing_psi_eq (hf : IsSmoothOnSpaceTime (ξ ω)) (y : ParabolicSpace) :
    hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y) (hairerPsiField N ξ ω) =
      hairerIPsiRecentred N ξ ω x y +
        ∑ k : Fin 3, shiftedPiGrad N ξ ω x k * (y.2 k - x.2 k) := by
  have hψ := isSmoothOnSpaceTime_hairerPsiField N hf
  have hc := IsSmoothOnSpaceTime.continuous hψ
  rw [hairerKernelIncrementPairing_eq N _ _ hc]
  unfold hairerIPsiRecentred shiftedPiGrad gammaFullGrad
  rw [hairerConvolution_comp_proj_eq N hc y, hairerConvolution_comp_proj_eq N hc x]
  simp_rw [hairerSpatialGradient_eq_integral_torusGrad N _ hψ x]
  have hrel : ∀ k : Fin 3, CanonicalData.relCoord x y k.succ = y.2 k - x.2 k := by
    intro k
    have hc4 : ∀ (z : ParabolicSpace) (j : Fin 3), parabolicCoords z j.succ = z.2 j := by
      intro z j
      fin_cases j <;> rfl
    simp [CanonicalData.relCoord, hc4]
  simp only [hrel]
  ring


theorem shiftedPi_row_iPsiCubePsi (hf : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiCubePsi) =
      fun y => hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiCube N ξ (C₁ C) ω) * hairerPsiField N ξ ω (spaceTimeProj y) := by
  rw [shiftedPi_row_treeField C x hf (τ := .iPsiCubePsi) (by simp [isFMinus])
    (fun i h => by cases h)]
  rfl

theorem shiftedPi_row_iPsiSqPsiSq (hf : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiSqPsiSq) =
      fun y => hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiSq N ξ (C₁ C) ω) * hairerTreePsiSq N ξ (C₁ C) ω (spaceTimeProj y) -
          C₂ C := by
  rw [shiftedPi_row_treeField C x hf (τ := .iPsiSqPsiSq) (by simp [isFMinus])
    (fun i h => by cases h)]
  rfl

theorem shiftedPi_row_iPsiCubePsiSq (hf : IsSmoothOnSpaceTime (ξ ω)) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiCubePsiSq) =
      fun y => hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiCube N ξ (C₁ C) ω) * hairerTreePsiSq N ξ (C₁ C) ω (spaceTimeProj y) -
          3 * C₂ C * hairerPsiField N ξ ω (spaceTimeProj y) := by
  rw [shiftedPi_row_treeField C x hf (τ := .iPsiCubePsiSq) (by simp [isFMinus])
    (fun i h => by cases h)]
  rfl

end RegularityStructures.Phi43

end
