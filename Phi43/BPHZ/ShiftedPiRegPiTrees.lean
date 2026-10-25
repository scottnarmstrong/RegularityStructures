/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiRegPi
import Mathlib.Tactic

/-!
# Shift identities for `Q_t Π_x τ (x)` on the positive-degree trees

Continuation of `ShiftedPiRegPi`: the symbols `I(Ψ³)`, `I(Ψ³)Ψ`, `I(Ψ²)Ψ²`, `I(Ψ³)Ψ²`, `I(Ψ)Ψ²`.
The coefficients involve the random gradients `shiftedPiGrad`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {C C' : RenormalisationConstants} {a b : ℝ} {t : ℝ} (x : ParabolicSpace)
  (hf : IsSmoothOnSpaceTime (ξ ω)) (hg : Statements.HasPhi43NoiseGrowth (ξ ω))

include hf hg

theorem shiftedPi_reg_iPsiPsiSq (ht : 0 < t) (h1 : C₁ C' = C₁ C + a) :
    shiftedPiReg N κ C' (ξ ω) x t .iPsiPsiSq =
      shiftedPiReg N κ C (ξ ω) x t .iPsiPsiSq - a * shiftedPiReg N κ C (ξ ω) x t .iPsi := by
  rw [shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht]
  have : shiftedPiVec (N := N) (κ := κ) x hf hg ht C' .iPsiPsiSq =
      shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiPsiSq +
        (-a) • shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsi :=
    Subtype.ext (funext fun y => by
      simp only [shiftedPiVec, Submodule.coe_add, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftedPi_shift_iPsiPsiSq x hf h1 y]
      ring)
  rw [this, map_add, map_smul]
  simp only [smul_eq_mul]
  ring

theorem shiftedPi_reg_iPsiSqPsiSq (ht : 0 < t) (h1 : C₁ C' = C₁ C + a) (h2 : C₂ C' = C₂ C + b) :
    shiftedPiReg N κ C' (ξ ω) x t .iPsiSqPsiSq =
      shiftedPiReg N κ C (ξ ω) x t .iPsiSqPsiSq - a * shiftedPiReg N κ C (ξ ω) x t .iPsiSq -
        b * shiftedPiMass t x := by
  rw [shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht]
  have : shiftedPiVec (N := N) (κ := κ) x hf hg ht C' .iPsiSqPsiSq =
      shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiSqPsiSq +
        (-a) • shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiSq +
        (-b) • shiftedPiVecOne x ht :=
    Subtype.ext (funext fun y => by
      simp only [shiftedPiVec, shiftedPiVecOne, Submodule.coe_add, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftedPi_shift_iPsiSqPsiSq x hf h1 h2 y]
      ring)
  rw [this, map_add, map_add, map_smul, map_smul, shiftedPiKernelInt_vecOne]
  simp only [smul_eq_mul]
  ring

theorem shiftedPi_reg_iPsiCube (ht : 0 < t) (h1 : C₁ C' = C₁ C + a) :
    shiftedPiReg N κ C' (ξ ω) x t .iPsiCube =
      shiftedPiReg N κ C (ξ ω) x t .iPsiCube -
        3 * a * (shiftedPiReg N κ C (ξ ω) x t .iPsi +
          ∑ k : Fin 3, shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k) := by
  rw [shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht]
  have : shiftedPiVec (N := N) (κ := κ) x hf hg ht C' .iPsiCube =
      shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiCube +
        (-(3 * a)) • (shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsi +
          shiftedPiGrad N ξ ω x 0 • shiftedPiVecCoord x ht 0 +
          shiftedPiGrad N ξ ω x 1 • shiftedPiVecCoord x ht 1 +
          shiftedPiGrad N ξ ω x 2 • shiftedPiVecCoord x ht 2) :=
    Subtype.ext (funext fun y => by
      have := shiftedPi_shift_iPsiCube (N := N) (κ := κ) x hf h1 y
      simp only [Fin.sum_univ_three] at this
      simp only [shiftedPiVec, shiftedPiVecCoord, Submodule.coe_add, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
      ring)
  rw [this, map_add, map_smul, map_add, map_add, map_add, map_smul, map_smul, map_smul]
  simp only [smul_eq_mul, shiftedPiKernelInt_vecCoord, Fin.sum_univ_three]
  ring

theorem shiftedPi_reg_iPsiCubePsi (ht : 0 < t) (h1 : C₁ C' = C₁ C + a) :
    shiftedPiReg N κ C' (ξ ω) x t .iPsiCubePsi =
      shiftedPiReg N κ C (ξ ω) x t .iPsiCubePsi -
        3 * a * (shiftedPiReg N κ C (ξ ω) x t .iPsiPsi +
          ∑ k : Fin 3, shiftedPiGrad N ξ ω x k * shiftedPiReg N κ C (ξ ω) x t (.psiX k)) := by
  rw [shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht, shiftedPi_reg_eq x hf hg ht]
  have : shiftedPiVec (N := N) (κ := κ) x hf hg ht C' .iPsiCubePsi =
      shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiCubePsi +
        (-(3 * a)) • (shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiPsi +
          shiftedPiGrad N ξ ω x 0 • shiftedPiVec (N := N) (κ := κ) x hf hg ht C (.psiX 0) +
          shiftedPiGrad N ξ ω x 1 • shiftedPiVec (N := N) (κ := κ) x hf hg ht C (.psiX 1) +
          shiftedPiGrad N ξ ω x 2 • shiftedPiVec (N := N) (κ := κ) x hf hg ht C (.psiX 2)) :=
    Subtype.ext (funext fun y => by
      have := shiftedPi_shift_iPsiCubePsi (N := N) (κ := κ) x hf h1 y
      simp only [Fin.sum_univ_three] at this
      simp only [shiftedPiVec, Submodule.coe_add, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
      ring)
  rw [this, map_add, map_smul, map_add, map_add, map_add, map_smul, map_smul, map_smul]
  simp only [smul_eq_mul, Fin.sum_univ_three, shiftedPi_reg_eq x hf hg ht]
  ring


theorem shiftedPi_reg_iPsiCubePsiSq (ht : 0 < t) (h1 : C₁ C' = C₁ C + a) (h2 : C₂ C' = C₂ C + b) :
    shiftedPiReg N κ C' (ξ ω) x t .iPsiCubePsiSq =
      shiftedPiReg N κ C (ξ ω) x t .iPsiCubePsiSq - a * shiftedPiReg N κ C (ξ ω) x t .iPsiCube -
        3 * a * shiftedPiReg N κ C (ξ ω) x t .iPsiPsiSq -
        3 * a * (∑ k : Fin 3, shiftedPiGrad N ξ ω x k *
          shiftedPiReg N κ C (ξ ω) x t (.psiSqX k)) +
        3 * a ^ 2 * (shiftedPiReg N κ C (ξ ω) x t .iPsi +
          ∑ k : Fin 3, shiftedPiGrad N ξ ω x k * shiftedPiMoment t x k) -
        3 * b * shiftedPiReg N κ C (ξ ω) x t .psi := by
  have e : ∀ τ, shiftedPiReg N κ C (ξ ω) x t τ =
      shiftedPiKernelInt t x (shiftedPiVec (N := N) (κ := κ) x hf hg ht C τ) :=
    fun τ => shiftedPi_reg_eq x hf hg ht C τ
  rw [shiftedPi_reg_eq x hf hg ht]
  simp only [e, Fin.sum_univ_three]
  have : shiftedPiVec (N := N) (κ := κ) x hf hg ht C' .iPsiCubePsiSq =
      shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiCubePsiSq +
        (-a) • shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiCube +
        (-(3 * a)) • shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsiPsiSq +
        (-(3 * a) * shiftedPiGrad N ξ ω x 0) •
          shiftedPiVec (N := N) (κ := κ) x hf hg ht C (.psiSqX 0) +
        (-(3 * a) * shiftedPiGrad N ξ ω x 1) •
          shiftedPiVec (N := N) (κ := κ) x hf hg ht C (.psiSqX 1) +
        (-(3 * a) * shiftedPiGrad N ξ ω x 2) •
          shiftedPiVec (N := N) (κ := κ) x hf hg ht C (.psiSqX 2) +
        (3 * a ^ 2) • shiftedPiVec (N := N) (κ := κ) x hf hg ht C .iPsi +
        (3 * a ^ 2 * shiftedPiGrad N ξ ω x 0) • shiftedPiVecCoord x ht 0 +
        (3 * a ^ 2 * shiftedPiGrad N ξ ω x 1) • shiftedPiVecCoord x ht 1 +
        (3 * a ^ 2 * shiftedPiGrad N ξ ω x 2) • shiftedPiVecCoord x ht 2 +
        (-(3 * b)) • shiftedPiVec (N := N) (κ := κ) x hf hg ht C .psi :=
    Subtype.ext (funext fun y => by
      have := shiftedPi_shift_iPsiCubePsiSq (N := N) (κ := κ) x hf h1 h2 y
      simp only [Fin.sum_univ_three] at this
      simp only [shiftedPiVec, shiftedPiVecCoord, Submodule.coe_add, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
      ring)
  rw [this]
  simp only [map_add, map_smul, smul_eq_mul, shiftedPiKernelInt_vecCoord]
  ring

end RegularityStructures.Phi43

end
