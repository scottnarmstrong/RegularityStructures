/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.Schwartz
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# One-dimensional kernels with symbol `exp(-t ξ^{2j})`

`symKernel j t b = ∫ exp(-t ξ^{2j}) cos(2π ξ b) dξ` is the real, even inverse Fourier transform of
the symbol `ξ ↦ exp(-t ξ^{2j})`. For `j = 1` it is a Gaussian (the 1D heat kernel) and for `j = 2`
it is the quartic kernel of `∂_t + ∂_b⁴`. For `t > 0` it is the (real part of the) Schwartz
function `𝓕⁻ (exp(-t ξ^{2j}))`; we prove continuity, integrability, `∫ = 1`, the semigroup
property `k_s ⋆ k_t = k_{s+t}` and rapid decay of `k_1` and `k_1'`, using
`Mathlib.Analysis.Distribution.SchwartzSpace.Fourier` and `Mathlib.Analysis.Fourier.Convolution`.
This is the 1D building block of the auxiliary semigroup of [Hos25, Example 2.7]
(arXiv:2310.07396v2).
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures

/-- The kernel with symbol `ξ ↦ exp(-t ξ^{2j})`:
`symKernel j t b = ∫ exp(-t ξ^{2j}) cos(2π ξ b) dξ`. -/
def symKernel (j : ℕ) (t b : ℝ) : ℝ :=
  ∫ ξ, Real.exp (-(t * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * b)

end RegularityStructures

end

public section

open MeasureTheory Real SchwartzMap
open scoped FourierTransform

namespace RegularityStructures

variable {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j)

/-- The Schwartz function `𝓕⁻ (ξ ↦ exp(-c ξ^{2j}))`. -/
@[expose] noncomputable def symSchwartz : 𝓢(ℝ, ℂ) := 𝓕⁻ (expPowSchwartz hc hj)

include hc in
theorem ofReal_symKernel (b : ℝ) : (symKernel j c b : ℂ) = symSchwartz hc hj b := by
  have hE : Integrable (expPowSchwartz hc hj) := (expPowSchwartz hc hj).integrable
  set F : ℝ → ℂ := fun ξ => Complex.exp (↑(2 * π * ξ * b) * Complex.I) *
    (Real.exp (-(c * ξ ^ (2 * j))) : ℂ) with hF
  have hS : symSchwartz hc hj b = ∫ ξ, F ξ := by
    rw [symSchwartz, fourierInv_coe, fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hF, smul_eq_mul, expPowSchwartz_apply]
    congr 3
    simp [mul_comm, mul_assoc, mul_left_comm]
  have hFi : Integrable F := by
    refine hE.norm.mono' (by fun_prop) (Filter.Eventually.of_forall fun ξ => ?_)
    show ‖F ξ‖ ≤ ‖expPowSchwartz hc hj ξ‖
    simp only [hF, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, expPowSchwartz_apply]
    exact le_rfl
  -- `∫ F` is real, since `F (-ξ) = conj (F ξ)` and `ξ ↦ ξ ^ (2 j)` is even
  have key : ∀ ξ, F (-ξ) = (starRingEnd ℂ) (F ξ) := by
    intro ξ
    have hexp : Complex.exp (↑(2 * π * -ξ * b) * Complex.I) =
        (starRingEnd ℂ) (Complex.exp (↑(2 * π * ξ * b) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    simp only [hF, map_mul, Complex.conj_ofReal, Even.neg_pow (even_two_mul j)]
    rw [hexp]
  have hconj : (starRingEnd ℂ) (∫ ξ, F ξ) = ∫ ξ, F ξ := by
    calc (starRingEnd ℂ) (∫ ξ, F ξ) = ∫ ξ, (starRingEnd ℂ) (F ξ) := integral_conj.symm
      _ = ∫ ξ, F (-ξ) := integral_congr_ae (Filter.Eventually.of_forall fun ξ => (key ξ).symm)
      _ = ∫ ξ, F ξ := integral_neg_eq_self F volume
  have hre : (∫ ξ, F ξ) = ((∫ ξ, F ξ).re : ℂ) := (Complex.conj_eq_iff_re.1 hconj).symm
  rw [hS, hre, symKernel]
  congr 1
  have hre2 := integral_re hFi
  simp only [RCLike.re_to_complex] at hre2
  rw [← hre2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [hF, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
  ring

include hc hj in
theorem symKernel_eq_re (b : ℝ) : symKernel j c b = (symSchwartz hc hj b).re := by
  rw [← ofReal_symKernel hc hj b, Complex.ofReal_re]

include hc hj in
theorem continuous_symKernel : Continuous (symKernel j c) := by
  have : symKernel j c = fun b => (symSchwartz hc hj b).re := funext (symKernel_eq_re hc hj)
  rw [this]
  exact Complex.continuous_re.comp (symSchwartz hc hj).continuous

include hc hj in
theorem fourier_symSchwartz : 𝓕 (symSchwartz hc hj) = expPowSchwartz hc hj :=
  FourierInvPair.fourier_fourierInv_eq _

include hc hj in
theorem integral_symKernel : ∫ b, symKernel j c b = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [ofReal_symKernel hc hj]
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) (fourier_symSchwartz hc hj)
  simp only [fourier_coe, expPowSchwartz_apply] at h
  rw [Real.fourier_eq] at h
  simpa [zero_pow (show 2 * j ≠ 0 by omega)] using h

/-- The semigroup property of the Schwartz kernels, in convolution form. -/
theorem convolution_symSchwartz {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (symSchwartz hs hj)
      (symSchwartz ht hj) = symSchwartz (add_pos hs ht) hj := by
  have h1 : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (symSchwartz hs hj)
      (symSchwartz ht hj) = 𝓕⁻ (pairing (ContinuousLinearMap.mul ℂ ℂ) (expPowSchwartz hs hj) (expPowSchwartz ht hj)) := by
    simp [SchwartzMap.convolution, fourier_symSchwartz]
  rw [h1, symSchwartz]
  congr 1
  ext x
  simp only [pairing_apply_apply, ContinuousLinearMap.mul_apply', expPowSchwartz_apply]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

include hj in
/-- The semigroup property `k_s ⋆ k_t = k_{s+t}` for the real kernels. -/
theorem integral_symKernel_mul_symKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a c : ℝ) :
    ∫ b, symKernel j s (a - b) * symKernel j t (b - c) = symKernel j (s + t) (a - c) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, ofReal_symKernel hs hj, ofReal_symKernel ht hj,
    ofReal_symKernel (add_pos hs ht) hj]
  have h2 := SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) (symSchwartz hs hj)
    (symSchwartz ht hj) (a - c)
  rw [convolution_symSchwartz hj hs ht] at h2
  rw [h2, MeasureTheory.convolution_def]
  rw [← integral_sub_left_eq_self (fun b => symSchwartz hs hj (a - b) * symSchwartz ht hj (b - c))
    volume a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel, ContinuousLinearMap.mul_apply']
  rw [sub_right_comm]

/-- A Schwartz function decays faster than any power: `(1 + |x|)^n ‖f x‖ ≤ C`. -/
theorem schwartz_exists_one_add_pow_mul_norm_le (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    ∃ C : ℝ, ∀ x, (1 + |x|) ^ n * ‖f x‖ ≤ C := by
  refine ⟨2 ^ n * (Finset.Iic (n, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f,
    fun x => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (n, 0)) (k := n) (n := 0)
    le_rfl le_rfl f x
  simpa using this

theorem abs_le_mul_one_add_rpow_neg {f : ℝ → ℝ} {g : ℝ → ℂ} (hfg : ∀ x, |f x| ≤ ‖g x‖)
    (hg : ∀ n : ℕ, ∃ C : ℝ, ∀ x, (1 + |x|) ^ n * ‖g x‖ ≤ C) (n : ℕ) :
    ∃ C : ℝ, ∀ x, |f x| ≤ C * (1 + |x|) ^ (-(n : ℝ)) := by
  obtain ⟨C, hC⟩ := hg n
  refine ⟨C, fun x => ?_⟩
  have hpos : 0 < (1 + |x|) ^ n := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc |f x| * (1 + |x|) ^ n ≤ ‖g x‖ * (1 + |x|) ^ n := by gcongr; exact hfg x
    _ = (1 + |x|) ^ n * ‖g x‖ := mul_comm _ _
    _ ≤ C := hC x

include hj in
/-- Rapid decay of `k_1`. -/
theorem symKernel_one_decay (n : ℕ) :
    ∃ C : ℝ, ∀ b, |symKernel j 1 b| ≤ C * (1 + |b|) ^ (-(n : ℝ)) :=
  abs_le_mul_one_add_rpow_neg (g := symSchwartz one_pos hj)
    (fun b => by
      rw [symKernel_eq_re one_pos hj]
      exact Complex.abs_re_le_norm _)
    (schwartz_exists_one_add_pow_mul_norm_le _) n

include hj in
theorem hasDerivAt_symKernel_one (b : ℝ) :
    HasDerivAt (symKernel j 1) (deriv (symSchwartz one_pos hj) b).re b := by
  have : symKernel j 1 = fun b => Complex.reCLM (symSchwartz one_pos hj b) :=
    funext (symKernel_eq_re one_pos hj)
  rw [this]
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt b ((symSchwartz one_pos hj).hasDerivAt b)

include hj in
theorem differentiable_symKernel_one : Differentiable ℝ (symKernel j 1) :=
  fun b => (hasDerivAt_symKernel_one hj b).differentiableAt

include hj in
/-- Rapid decay of `k_1'`. -/
theorem deriv_symKernel_one_decay (n : ℕ) :
    ∃ C : ℝ, ∀ b, |deriv (symKernel j 1) b| ≤ C * (1 + |b|) ^ (-(n : ℝ)) :=
  abs_le_mul_one_add_rpow_neg (g := derivCLM ℝ ℂ (symSchwartz one_pos hj))
    (fun b => by
      rw [(hasDerivAt_symKernel_one hj b).deriv, derivCLM_apply]
      exact Complex.abs_re_le_norm _)
    (schwartz_exists_one_add_pow_mul_norm_le _) n

end RegularityStructures

end
