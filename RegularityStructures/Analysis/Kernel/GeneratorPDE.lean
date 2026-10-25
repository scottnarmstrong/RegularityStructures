/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorKernel

/-!
# Directional derivatives of the parabolic kernel and its heat equation
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem dirDeriv_time_kernelDerivs {t : ℝ} (ht : 0 < t) (a b₀ b₁ b₂ : ℕ) :
    dirDeriv timeDir (kernelDerivs t a b₀ b₁ b₂) = kernelDerivs t (a + 1) b₀ b₁ b₂ := by
  funext w
  rw [dirDeriv_eq_deriv_line (contDiff_kernelDerivs ht a b₀ b₁ b₂)]
  have e : (fun s : ℝ => kernelDerivs t a b₀ b₁ b₂ (w + s • timeDir)) = fun s =>
      iteratedDeriv a (symKernel 1 t) (w.1 + s) *
        (iteratedDeriv b₀ (symKernel 2 t) (w.2 0) * iteratedDeriv b₁ (symKernel 2 t) (w.2 1) *
          iteratedDeriv b₂ (symKernel 2 t) (w.2 2)) := by
    funext s
    simp [kernelDerivs, timeDir]
  rw [e]
  have h := ((hasDerivAt_iteratedDeriv_symKernel ht one_pos a (w.1 + 0)).comp_const_add w.1 0
    ).mul_const (iteratedDeriv b₀ (symKernel 2 t) (w.2 0) * iteratedDeriv b₁ (symKernel 2 t) (w.2 1) *
          iteratedDeriv b₂ (symKernel 2 t) (w.2 2))
  rw [h.deriv]
  simp [kernelDerivs]

theorem dirDeriv_space0_kernelDerivs {t : ℝ} (ht : 0 < t) (a b₀ b₁ b₂ : ℕ) :
    dirDeriv (spaceDir 0) (kernelDerivs t a b₀ b₁ b₂) = kernelDerivs t a (b₀ + 1) b₁ b₂ := by
  funext w
  rw [dirDeriv_eq_deriv_line (contDiff_kernelDerivs ht a b₀ b₁ b₂)]
  have e : (fun s : ℝ => kernelDerivs t a b₀ b₁ b₂ (w + s • spaceDir 0)) = fun s =>
      iteratedDeriv a (symKernel 1 t) w.1 *
        (iteratedDeriv b₀ (symKernel 2 t) (w.2 0 + s) * iteratedDeriv b₁ (symKernel 2 t) (w.2 1) *
          iteratedDeriv b₂ (symKernel 2 t) (w.2 2)) := by
    funext s
    simp [kernelDerivs, spaceDir]
  rw [e]
  have h := (((hasDerivAt_iteratedDeriv_symKernel ht two_pos b₀ (w.2 0 + 0)).comp_const_add
    (w.2 0) 0).mul_const (iteratedDeriv b₁ (symKernel 2 t) (w.2 1))).mul_const
      (iteratedDeriv b₂ (symKernel 2 t) (w.2 2))
  rw [(h.const_mul (iteratedDeriv a (symKernel 1 t) w.1)).deriv]
  simp [kernelDerivs]

theorem dirDeriv_space1_kernelDerivs {t : ℝ} (ht : 0 < t) (a b₀ b₁ b₂ : ℕ) :
    dirDeriv (spaceDir 1) (kernelDerivs t a b₀ b₁ b₂) = kernelDerivs t a b₀ (b₁ + 1) b₂ := by
  funext w
  rw [dirDeriv_eq_deriv_line (contDiff_kernelDerivs ht a b₀ b₁ b₂)]
  have e : (fun s : ℝ => kernelDerivs t a b₀ b₁ b₂ (w + s • spaceDir 1)) = fun s =>
      iteratedDeriv a (symKernel 1 t) w.1 *
        (iteratedDeriv b₀ (symKernel 2 t) (w.2 0) * iteratedDeriv b₁ (symKernel 2 t) (w.2 1 + s) *
          iteratedDeriv b₂ (symKernel 2 t) (w.2 2)) := by
    funext s
    simp [kernelDerivs, spaceDir]
  rw [e]
  have h := (((hasDerivAt_iteratedDeriv_symKernel ht two_pos b₁ (w.2 1 + 0)).comp_const_add
    (w.2 1) 0).const_mul (iteratedDeriv b₀ (symKernel 2 t) (w.2 0))).mul_const
      (iteratedDeriv b₂ (symKernel 2 t) (w.2 2))
  rw [(h.const_mul (iteratedDeriv a (symKernel 1 t) w.1)).deriv]
  simp [kernelDerivs]

theorem dirDeriv_space2_kernelDerivs {t : ℝ} (ht : 0 < t) (a b₀ b₁ b₂ : ℕ) :
    dirDeriv (spaceDir 2) (kernelDerivs t a b₀ b₁ b₂) = kernelDerivs t a b₀ b₁ (b₂ + 1) := by
  funext w
  rw [dirDeriv_eq_deriv_line (contDiff_kernelDerivs ht a b₀ b₁ b₂)]
  have e : (fun s : ℝ => kernelDerivs t a b₀ b₁ b₂ (w + s • spaceDir 2)) = fun s =>
      iteratedDeriv a (symKernel 1 t) w.1 *
        (iteratedDeriv b₀ (symKernel 2 t) (w.2 0) * iteratedDeriv b₁ (symKernel 2 t) (w.2 1) *
          iteratedDeriv b₂ (symKernel 2 t) (w.2 2 + s)) := by
    funext s
    simp [kernelDerivs, spaceDir]
  rw [e]
  have h := ((hasDerivAt_iteratedDeriv_symKernel ht two_pos b₂ (w.2 2 + 0)).comp_const_add
    (w.2 2) 0).const_mul (iteratedDeriv b₀ (symKernel 2 t) (w.2 0) *
      iteratedDeriv b₁ (symKernel 2 t) (w.2 1))
  rw [(h.const_mul (iteratedDeriv a (symKernel 1 t) w.1)).deriv]
  simp [kernelDerivs, mul_assoc]

/-- The pointwise heat equation `∂_t q_t = L q_t` for the parabolic kernel. -/
theorem parabolicTimeDeriv_eq {t : ℝ} (ht : 0 < t) (w : ParabolicSpace) :
    parabolicTimeDeriv t w =
      generatorTimeCoeff * (dirDeriv timeDir)^[2] (parabolicKernel t) w -
        generatorSpaceCoeff * ∑ i : Fin 3, (dirDeriv (spaceDir i))^[4] (parabolicKernel t) w := by
  rw [parabolicKernel_eq_kernelDerivs, Fin.sum_univ_three]
  simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id,
    dirDeriv_time_kernelDerivs ht, dirDeriv_space0_kernelDerivs ht,
    dirDeriv_space1_kernelDerivs ht, dirDeriv_space2_kernelDerivs ht]
  unfold parabolicTimeDeriv kernelDerivs
  rw [symKernelTimeDeriv_one_eq ht, symKernelTimeDeriv_two_eq ht, symKernelTimeDeriv_two_eq ht,
    symKernelTimeDeriv_two_eq ht]
  simp only [iteratedDeriv_zero, heatKernel1D, quarticKernel]
  ring

end RegularityStructures

end
