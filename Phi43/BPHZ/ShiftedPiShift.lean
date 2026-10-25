/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiRows
import Mathlib.Tactic

/-!
# Pointwise shift identities for the extension `Π`

Let `C' ` and `C` be constants with `C₁ C' = C₁ C + a` and `C₂ C' = C₂ C + b`.  For every symbol
off the polynomial sector, `Π^{C'}_x τ` is `Π^{C}_x τ` plus an explicit combination of the rows
`Π^{C}_x σ` with `deg σ ≥ deg τ` (Hai14 (8.39)), whose coefficients are polynomials in `a, b` and in
the random gradients `gₖ = ∂ₖ(K ∗ Ψ)(x)` (the pairing of `Ψ` against the kernel increment is the
recentred row `Π_x I(Ψ)` plus `∑ₖ gₖ (yₖ - xₖ)`).  The row of `I(Ψ³)²` is the square of the row
of `I(Ψ³)`, which shifts by `-3a ⟨K̃, Ψ⟩`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {C C' : RenormalisationConstants} {a b : ℝ} (x : ParabolicSpace)

private theorem shiftedPi_continuous_psi (hf : IsSmoothOnSpaceTime (ξ ω)) :
    Continuous (hairerPsiField N ξ ω) :=
  continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hf)

/-- The pairing of the kernel increment with the Wick cube of constant `c`. -/
theorem shiftedPi_pair_treePsiCube (hf : IsSmoothOnSpaceTime (ξ ω)) (c : ℝ) (y : ParabolicSpace) :
    hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiCube N ξ c ω) =
      hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
          (fun w => hairerPsiField N ξ ω w ^ 3) -
        3 * c * hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
          (hairerPsiField N ξ ω) := by
  have hΨ := shiftedPi_continuous_psi (N := N) hf
  have h := hairerKernelIncrementPairing_sub_const_mul N (spaceTimeProj x) (spaceTimeProj y)
    (f := fun w => hairerPsiField N ξ ω w ^ 3) (g := hairerPsiField N ξ ω) (by fun_prop) hΨ
    (3 * c)
  unfold hairerTreePsiCube
  exact h

/-- The constant in the Wick square does not matter for the pairing. -/
theorem shiftedPi_pair_treePsiSq (hf : IsSmoothOnSpaceTime (ξ ω)) (c : ℝ) (y : ParabolicSpace) :
    hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiSq N ξ c ω) =
      hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) := by
  have hΨ := shiftedPi_continuous_psi (N := N) hf
  have h := hairerKernelIncrementPairing_sub_const_mul N (spaceTimeProj x) (spaceTimeProj y)
    (f := fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) (g := fun _ => (1 : ℝ))
    (by fun_prop) continuous_const c
  have h1 : hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
      (fun _ => (1 : ℝ)) = 0 := by
    unfold hairerKernelIncrementPairing
    simpa using integral_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y)
  rw [h1, mul_zero, sub_zero] at h
  unfold hairerTreePsiSq
  simp only [sq, mul_one] at h ⊢
  exact h

local notation "Ext" => CanonicalData.renormalisedExtensionPi

theorem shiftedPi_shift_psi (hf : IsSmoothOnSpaceTime (ξ ω)) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .psi) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .psi) y := by
  rw [shiftedPi_row_treeField C' x hf (τ := .psi) (by simp [isFMinus]) (fun i h => by cases h),
    shiftedPi_row_treeField C x hf (τ := .psi) (by simp [isFMinus]) (fun i h => by cases h)]
  rfl

theorem shiftedPi_shift_psiSq (hf : IsSmoothOnSpaceTime (ξ ω)) (h1 : C₁ C' = C₁ C + a)
    (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .psiSq) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .psiSq) y - a := by
  rw [shiftedPi_row_treeField C' x hf (τ := .psiSq) (by simp [isFMinus]) (fun i h => by cases h),
    shiftedPi_row_treeField C x hf (τ := .psiSq) (by simp [isFMinus]) (fun i h => by cases h)]
  simp only [hairerTreeField, hairerTreePsiSq, h1]
  ring

theorem shiftedPi_shift_psiCube (hf : IsSmoothOnSpaceTime (ξ ω)) (h1 : C₁ C' = C₁ C + a)
    (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .psiCube) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .psiCube) y -
      3 * a * (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .psi) y := by
  rw [shiftedPi_row_treeField C' x hf (τ := .psiCube) (by simp [isFMinus]) (fun i h => by cases h),
    shiftedPi_row_treeField C x hf (τ := .psiCube) (by simp [isFMinus]) (fun i h => by cases h),
    shiftedPi_row_treeField C x hf (τ := .psi) (by simp [isFMinus]) (fun i h => by cases h)]
  simp only [hairerTreeField, hairerTreePsiCube, h1]
  ring

theorem shiftedPi_shift_psiSqX (hf : IsSmoothOnSpaceTime (ξ ω)) (h1 : C₁ C' = C₁ C + a)
    (i : Fin 3) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis (.psiSqX i)) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis (.psiSqX i)) y - a * (y.2 i - x.2 i) := by
  rw [shiftedPi_row_psiSqX C' x hf i, shiftedPi_row_psiSqX C x hf i]
  simp only [hairerTreePsiSq, h1]
  ring

theorem shiftedPi_shift_psiX (hf : IsSmoothOnSpaceTime (ξ ω)) (i : Fin 3) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis (.psiX i)) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis (.psiX i)) y := by
  rw [extensionPi_psiX_eq hf, extensionPi_psiX_eq hf]

theorem shiftedPi_shift_iPsiSq (hf : IsSmoothOnSpaceTime (ξ ω)) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .iPsiSq) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiSq) y := by
  rw [extensionPi_iPsiSq_eq hf, extensionPi_iPsiSq_eq hf]

theorem shiftedPi_shift_iPsiPsi (hf : IsSmoothOnSpaceTime (ξ ω)) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .iPsiPsi) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiPsi) y := by
  rw [extensionPi_iPsiPsi_eq hf, extensionPi_iPsiPsi_eq hf]

theorem shiftedPi_shift_iPsiSqPsi (hf : IsSmoothOnSpaceTime (ξ ω)) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .iPsiSqPsi) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiSqPsi) y := by
  rw [extensionPi_iPsiSqPsi_eq hf, extensionPi_iPsiSqPsi_eq hf]

theorem shiftedPi_shift_iPsiPsiSq (hf : IsSmoothOnSpaceTime (ξ ω)) (h1 : C₁ C' = C₁ C + a)
    (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .iPsiPsiSq) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiPsiSq) y -
      a * (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .iPsi) y := by
  rw [extensionPi_iPsiPsiSq_eq hf, extensionPi_iPsiPsiSq_eq hf, extensionPi_iPsi_eq hf]
  simp only [hairerTreePsiSq, h1]
  ring

theorem shiftedPi_shift_iPsiCube (hf : IsSmoothOnSpaceTime (ξ ω)) (h1 : C₁ C' = C₁ C + a)
    (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .iPsiCube) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiCube) y -
      3 * a * ((hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .iPsi) y +
        ∑ k : Fin 3, shiftedPiGrad N ξ ω x k * (y.2 k - x.2 k)) := by
  rw [extensionPi_iPsiCube_eq hf, extensionPi_iPsiCube_eq hf, extensionPi_iPsi_eq hf]
  simp only [shiftedPi_pair_treePsiCube x hf, h1]
  rw [shiftedPi_pairing_psi_eq x hf]
  ring

theorem shiftedPi_shift_iPsiCubePsi (hf : IsSmoothOnSpaceTime (ξ ω)) (h1 : C₁ C' = C₁ C + a)
    (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .iPsiCubePsi) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiCubePsi) y -
      3 * a * ((hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .iPsiPsi) y +
        ∑ k : Fin 3, shiftedPiGrad N ξ ω x k * (hairerCanonicalData (κ := κ) N
          (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis (.psiX k)) y) := by
  rw [shiftedPi_row_iPsiCubePsi C' x hf, shiftedPi_row_iPsiCubePsi C x hf,
    extensionPi_iPsiPsi_eq hf]
  simp only [extensionPi_psiX_eq hf]
  simp only [shiftedPi_pair_treePsiCube x hf, h1]
  rw [shiftedPi_pairing_psi_eq x hf]
  simp only [Fin.sum_univ_three]
  ring

theorem shiftedPi_shift_iPsiSqPsiSq (hf : IsSmoothOnSpaceTime (ξ ω)) (h1 : C₁ C' = C₁ C + a)
    (h2 : C₂ C' = C₂ C + b) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .iPsiSqPsiSq) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiSqPsiSq) y -
      a * (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .iPsiSq) y - b := by
  rw [shiftedPi_row_iPsiSqPsiSq C' x hf, shiftedPi_row_iPsiSqPsiSq C x hf,
    extensionPi_iPsiSq_eq hf]
  simp only [shiftedPi_pair_treePsiSq x hf, h2]
  simp only [hairerTreePsiSq, h1]
  ring

theorem shiftedPi_shift_iPsiCubePsiSq (hf : IsSmoothOnSpaceTime (ξ ω)) (h1 : C₁ C' = C₁ C + a)
    (h2 : C₂ C' = C₂ C + b) (y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C' x (basis .iPsiCubePsiSq) y =
      (hairerCanonicalData (κ := κ) N (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi
        C x (basis .iPsiCubePsiSq) y -
      a * (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .iPsiCube) y -
      3 * a * (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .iPsiPsiSq) y -
      3 * a * (∑ k : Fin 3, shiftedPiGrad N ξ ω x k * (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis (.psiSqX k)) y) +
      3 * a ^ 2 * ((hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .iPsi) y +
        ∑ k : Fin 3, shiftedPiGrad N ξ ω x k * (y.2 k - x.2 k)) -
      3 * b * (hairerCanonicalData (κ := κ) N
        (canonicalNoiseOfSpaceTime (ξ ω) hf)).renormalisedExtensionPi C x (basis .psi) y := by
  rw [shiftedPi_row_iPsiCubePsiSq C' x hf, shiftedPi_row_iPsiCubePsiSq C x hf,
    extensionPi_iPsiCube_eq hf, extensionPi_iPsiPsiSq_eq hf,
    extensionPi_iPsi_eq hf, shiftedPi_row_treeField C x hf (τ := .psi) (by simp [isFMinus])
      (fun i h => by cases h)]
  simp only [shiftedPi_row_psiSqX C x hf]
  simp only [shiftedPi_pair_treePsiCube x hf, h2]
  rw [shiftedPi_pairing_psi_eq x hf]
  simp only [hairerTreeField, hairerTreePsiSq, h1, Fin.sum_univ_three]
  ring

end RegularityStructures.Phi43

end
