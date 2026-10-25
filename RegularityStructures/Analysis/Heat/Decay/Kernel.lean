/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decay.KernelDeriv
public import RegularityStructures.Analysis.Heat.Decay.Estimate
public import RegularityStructures.Analysis.Heat.Decay.Nonpos
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Spatial decay of every derivative of the heat kernel

For every finite list of directions `L`, every `m` and every `T₀`, there is `C` with
`|D_L G (t, x)| ≤ C |x|^{-2m}` whenever `t ≤ T₀` and `|x| ≥ 1`
(`exists_abs_lineIter_heatKernelR4_le_of_list`, and `exists_abs_lineIter_heatKernelR4_le` along
`multiDirs k`).  For `t > 0` the derivative is `P(t⁻¹, x) G` with `P` a polynomial
(`exists_lineIter_heatKernelR4`) which is beaten by the Gaussian factor; for `t ≤ 0` it vanishes.
-/

public section

namespace RegularityStructures

theorem exists_abs_lineIter_heatKernelR4_le_of_list (L : List ParabolicSpace) (m : ℕ)
    {T₀ : ℝ} : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, z.1 ≤ T₀ → 1 ≤ sqNorm3 z.2 →
      |lineIter L heatKernelR4 z| ≤ C * (sqNorm3 z.2)⁻¹ ^ m := by
  obtain ⟨P, hP, hPz⟩ := exists_lineIter_heatKernelR4 L
  obtain ⟨a, C1, hC1, hb⟩ := hP.exists_bound
  set T : ℝ := max T₀ 1 with hT
  have hTpos : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨C2, hC2, hcore⟩ := exists_bound_pow_mul_exp_neg (a + 2) a m (inv_pos.2 hTpos)
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun z hzT hS => ?_⟩
  have hSpos : 0 < sqNorm3 z.2 := lt_of_lt_of_le one_pos hS
  by_cases ht : 0 < z.1
  · rw [hPz z ht, abs_mul, abs_of_nonneg (heatKernelR4_nonneg z), heatKernelR4_of_pos ht]
    set w : ℝ := z.1⁻¹ with hw
    set r : ℝ := sqNorm3 z.2 with hr
    have hwpos : 0 < w := inv_pos.2 ht
    have hw0 : T⁻¹ ≤ w := inv_anti₀ ht (hzT.trans (le_max_left _ _))
    have hG : gaussKernel z.1 z.2 ≤ (1 + w) ^ 2 * Real.exp (-(r * w / 4)) := by
      unfold gaussKernel
      have he : -sqNorm3 z.2 / (4 * z.1) = -(r * w / 4) := by
        rw [hw, hr]; field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_right (rpow_neg_three_halves_le ht) (Real.exp_pos _).le
    have hGnn : 0 ≤ gaussKernel z.1 z.2 := gaussKernel_nonneg ht _
    have h1 : |P z| * gaussKernel z.1 z.2 ≤
        (C1 * ((1 + w) ^ a * (1 + r) ^ a)) * ((1 + w) ^ 2 * Real.exp (-(r * w / 4))) :=
      mul_le_mul (hb z ht) hG hGnn (mul_nonneg hC1 (by positivity))
    have h2 := hcore w r hw0 hS
    have hrm : r ^ m * (r⁻¹) ^ m = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hSpos.ne', one_pow]
    calc |P z| * gaussKernel z.1 z.2
        ≤ (C1 * ((1 + w) ^ a * (1 + r) ^ a)) * ((1 + w) ^ 2 * Real.exp (-(r * w / 4))) := h1
      _ = C1 * (((1 + w) ^ (a + 2) * (1 + r) ^ a * r ^ m * Real.exp (-(r * w / 4))) *
            (r⁻¹) ^ m) := by
        rw [pow_add]
        linear_combination (-(C1 * ((1 + w) ^ a * (1 + w) ^ 2 * (1 + r) ^ a *
          Real.exp (-(r * w / 4))))) * hrm
      _ ≤ C1 * (C2 * (r⁻¹) ^ m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) hC1
      _ = C1 * C2 * (r⁻¹) ^ m := by ring
  · rw [lineIter_heatKernelR4_eq_zero_of_nonpos L (not_lt.1 ht) hSpos]
    simp only [abs_zero]
    positivity

end RegularityStructures

end
