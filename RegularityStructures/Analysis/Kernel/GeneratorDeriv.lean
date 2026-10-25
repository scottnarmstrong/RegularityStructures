/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorSymbol
public import RegularityStructures.Analysis.Kernel.SymbolDeriv
public import RegularityStructures.Analysis.Parabolic.Generator

/-!
# The 1D heat equations for the symbol kernels

For `t > 0`: `k_t = symKernel j t` is smooth, `k_t'' = -4π² C_2`, `k_t'''' = 16π⁴ C_4`, and
`∂_t k_t = -C_{2j}`. Hence
`∂_t g_t = (4π²)⁻¹ g_t''` (`j = 1`) and `∂_t k_t = -(16π⁴)⁻¹ k_t''''` (`j = 2`), i.e. the
coefficients `generatorTimeCoeff = (4π²)⁻¹` and `generatorSpaceCoeff = (16π⁴)⁻¹` of
`RegularityStructures.Analysis.Parabolic.Generator` are the correct ones for the normalisation
`symKernel j t b = ∫ exp(-t ξ^{2j}) cos(2π ξ b) dξ`.
-/

public section

open MeasureTheory Real

namespace RegularityStructures

open scoped ContDiff

theorem contDiff_symKernel {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : 0 < j) :
    ContDiff ℝ ∞ (symKernel j t) := by
  have : symKernel j t = fun b => (symSchwartz ht hj b).re := funext (symKernel_eq_re ht hj)
  rw [this]
  exact Complex.reCLM.contDiff.comp ((symSchwartz ht hj).smooth _)

theorem hasDerivAt_symKernel_b {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : 0 < j) (b : ℝ) :
    HasDerivAt (symKernel j t) (-(2 * π) * symSin j 1 t b) b := by
  have : symKernel j t = fun b => symCos j 0 t b := funext (symKernel_eq_symCos j t)
  rw [this]
  exact hasDerivAt_symCos_b ht hj 0 b

theorem iteratedDeriv_symKernel_two {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : 0 < j) :
    iteratedDeriv 2 (symKernel j t) = fun b => -(2 * π) * (2 * π) * symCos j 2 t b := by
  have h1 : iteratedDeriv 1 (symKernel j t) = fun b => -(2 * π) * symSin j 1 t b := by
    rw [iteratedDeriv_one]
    exact funext fun b => (hasDerivAt_symKernel_b ht hj b).deriv
  rw [iteratedDeriv_succ, h1]
  funext b
  refine (((hasDerivAt_symSin_b ht hj 1 b).const_mul (-(2 * π))).deriv).trans ?_
  ring

theorem iteratedDeriv_symKernel_four {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : 0 < j) :
    iteratedDeriv 4 (symKernel j t) = fun b => 16 * π ^ 4 * symCos j 4 t b := by
  have h2 := iteratedDeriv_symKernel_two ht hj
  have h3 : iteratedDeriv 3 (symKernel j t) =
      fun b => -(2 * π) * (2 * π) * (-(2 * π) * symSin j 3 t b) := by
    rw [iteratedDeriv_succ, h2]
    funext b
    exact (((hasDerivAt_symCos_b ht hj 2 b).const_mul (-(2 * π) * (2 * π))).deriv)
  rw [iteratedDeriv_succ, h3]
  funext b
  refine ((((hasDerivAt_symSin_b ht hj 3 b).const_mul (-(2 * π))).const_mul
    (-(2 * π) * (2 * π))).deriv).trans ?_
  ring

theorem symKernelTimeDeriv_eq {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : 0 < j) (b : ℝ) :
    symKernelTimeDeriv j t b = -symCos j (2 * j) t b := by
  have h1 := hasDerivAt_symKernel_time hj ht b
  have h2 := hasDerivAt_symCos_t ht hj 0 b
  have e : (fun s => symKernel j s b) = fun s => symCos j 0 s b :=
    funext fun s => symKernel_eq_symCos j s b
  rw [e] at h1
  simpa using h1.unique h2

/-- The heat equation `∂_t g_t = (4π²)⁻¹ g_t''`. -/
theorem symKernelTimeDeriv_one_eq {t : ℝ} (ht : 0 < t) (b : ℝ) :
    symKernelTimeDeriv 1 t b = generatorTimeCoeff * iteratedDeriv 2 (symKernel 1 t) b := by
  rw [symKernelTimeDeriv_eq ht one_pos, iteratedDeriv_symKernel_two ht one_pos]
  unfold generatorTimeCoeff
  have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  simp only [mul_one]
  field_simp
  ring

/-- The heat equation `∂_t k_t = -(16π⁴)⁻¹ k_t''''`. -/
theorem symKernelTimeDeriv_two_eq {t : ℝ} (ht : 0 < t) (b : ℝ) :
    symKernelTimeDeriv 2 t b = -(generatorSpaceCoeff * iteratedDeriv 4 (symKernel 2 t) b) := by
  rw [symKernelTimeDeriv_eq ht two_pos, iteratedDeriv_symKernel_four ht two_pos]
  unfold generatorSpaceCoeff
  have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  norm_num
  field_simp

end RegularityStructures

end
