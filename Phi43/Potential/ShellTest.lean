/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.ShellExp
public import Phi43.Potential.PairingGeneric
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Analysis.Heat.Decomposition.Basic

/-!
# The shells `(1 - e^{-t}) heatShell n` as scaled test functions

`potShellKernel n w = (1 - e^{-w₀}) heatShell n w`.  For every base point `z`,
`y ↦ potShellKernel n (z - y)` is a test function scaled at `z` with radius `2^{-n}` and constant
`potShellConst n = 48 M / 2^{-n}`, `M = potKernelConst (heatShell 0)` (`isScaledTest_potShell`): the
factor `(1 - e^{-t})` is `O(2^{-2n})` with all derivatives in scaled coordinates, which turns the
amplitude `2^{3n}` of the shell into `2^{n}`.
-/

open scoped ContDiff

public section

open Set

namespace RegularityStructures.Potential

/-- The `n`-th shell of `(1 - e^{-t}) G`. -/
@[expose] noncomputable def potShellKernel (n : ℕ) (w : ParabolicSpace) : ℝ :=
  (1 - Real.exp (-w.1)) * heatShell n w

theorem isUnitKernel_heatShell_zero : IsUnitKernel (heatShell 0) where
  smooth := contDiff_heatShell 0
  supp w hw := heatShell_eq_zero (by simpa using hw)

/-- The constant of the scaled bound of the `n`-th shell. -/
@[expose] noncomputable def potShellConst (n : ℕ) : ℝ :=
  48 * potKernelConst (heatShell 0) / (2⁻¹ : ℝ) ^ n

theorem potShellConst_pos (n : ℕ) : 0 < potShellConst n := by
  have := potKernelConst_pos isUnitKernel_heatShell_zero
  unfold potShellConst; positivity

theorem potShellKernel_scaled (n : ℕ) (v : ParabolicSpace) :
    potShellKernel n (-(parabolicDilate ((2 : ℝ)⁻¹ ^ n) v)) =
      ((2 : ℝ) ^ n) ^ 3 * ((1 - Real.exp (((2 : ℝ)⁻¹ ^ n) ^ 2 * v.1)) * heatShell 0 (-v)) := by
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  unfold potShellKernel
  rw [heatShell_eq_scale n]
  have e : parabolicDilate ((2 : ℝ) ^ n) (-(parabolicDilate ((2 : ℝ)⁻¹ ^ n) v)) = -v := by
    have : (2 : ℝ)⁻¹ ^ n = ((2 : ℝ) ^ n)⁻¹ := inv_pow _ _
    rw [this]
    have h2 : parabolicDilate ((2 : ℝ) ^ n) (-(parabolicDilate ((2 : ℝ) ^ n)⁻¹ v)) =
        -(parabolicDilate ((2 : ℝ) ^ n) (parabolicDilate ((2 : ℝ) ^ n)⁻¹ v)) := by
      ext <;> simp [parabolicDilate]
    rw [h2, parabolicDilate_parabolicDilate_inv hc.ne']
  rw [e]
  have h1 : (-(parabolicDilate ((2 : ℝ)⁻¹ ^ n) v)).1 = -(((2 : ℝ)⁻¹ ^ n) ^ 2 * v.1) := by
    simp [parabolicDilate]
  rw [h1, neg_neg]
  ring

theorem iteratedFDeriv_heatShell_neg_eq_zero (k : ℕ) {v : ParabolicSpace}
    (hv : 1 < parabolicNorm v) : iteratedFDeriv ℝ k (fun v => heatShell 0 (-v)) v = 0 := by
  have hs : tsupport (fun v : ParabolicSpace => heatShell 0 (-v)) ⊆
      {w | parabolicNorm w ≤ 1} := by
    refine closure_minimal (fun w hw => ?_)
      (isClosed_le continuous_parabolicNorm continuous_const)
    by_contra h
    exact hw (heatShell_eq_zero (by simpa [parabolicNorm_neg] using not_le.1 h))
  by_contra hne
  exact absurd (hs (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := k) hne)) (not_le.2 hv)

theorem norm_iteratedFDeriv_potShell_scaled_le (n : ℕ) {k : ℕ} (hk : k ≤ 4) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ k (fun v => potShellKernel n (-(parabolicDilate ((2 : ℝ)⁻¹ ^ n) v))) v‖ ≤
      potShellConst n := by
  set R : ℝ := (2 : ℝ)⁻¹ ^ n with hR
  have hR0 : 0 < R := by positivity
  have hR1 : R ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hH : ContDiff ℝ ∞ (fun v : ParabolicSpace => heatShell 0 (-v)) :=
    (contDiff_heatShell 0).comp contDiff_neg
  have hF : ContDiff ℝ ∞ (fun v : ParabolicSpace => 1 - Real.exp (R ^ 2 * v.1)) :=
    contDiff_const.sub (contDiff_expTime _)
  have e : (fun v => potShellKernel n (-(parabolicDilate R v))) =
      fun v => ((2 : ℝ) ^ n) ^ 3 • ((1 - Real.exp (R ^ 2 * v.1)) * heatShell 0 (-v)) := by
    funext v
    rw [hR, potShellKernel_scaled, smul_eq_mul]
  rw [e, iteratedFDeriv_const_smul_apply' ((hF.mul hH).contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul]
  have hM : ∀ j ≤ 4, ∀ v : ParabolicSpace, ‖iteratedFDeriv ℝ j (fun v => heatShell 0 (-v)) v‖ ≤
      potKernelConst (heatShell 0) := fun j hj v =>
    iteratedFDeriv_refl_le isUnitKernel_heatShell_zero hj v
  have hMpos := potKernelConst_pos isUnitKernel_heatShell_zero
  have hprod : ‖iteratedFDeriv ℝ k (fun v : ParabolicSpace =>
      (1 - Real.exp (R ^ 2 * v.1)) * heatShell 0 (-v)) v‖ ≤ 48 * R ^ 2 * potKernelConst (heatShell 0) := by
    refine (_root_.norm_iteratedFDeriv_mul_le (N := k) (hF.of_le (by exact_mod_cast le_top))
      (hH.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl k)).trans ?_
    by_cases hv : parabolicNorm v ≤ 1
    · have hb : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i
          (fun v : ParabolicSpace => 1 - Real.exp (R ^ 2 * v.1)) v‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun v : ParabolicSpace => heatShell 0 (-v)) v‖ ≤
          k.choose i * (3 * R ^ 2 * potKernelConst (heatShell 0)) := by
        intro i hi
        have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul
          (norm_iteratedFDeriv_one_sub_expTime_le (by positivity) (pow_le_one₀ hR0.le hR1) i hv)
          (hM (k - i) (by omega) v) (norm_nonneg _) (by positivity)) (Nat.cast_nonneg _)
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.sum_mul]
      have h2 : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [h2]
      have : (2 : ℝ) ^ k ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      have hp : 0 ≤ 3 * R ^ 2 * potKernelConst (heatShell 0) := by positivity
      nlinarith
    · push Not at hv
      have : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i
          (fun v : ParabolicSpace => 1 - Real.exp (R ^ 2 * v.1)) v‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun v : ParabolicSpace => heatShell 0 (-v)) v‖ = 0 := by
        intro i _
        rw [iteratedFDeriv_heatShell_neg_eq_zero _ hv]; simp
      rw [Finset.sum_eq_zero this]
      positivity
  have hpow : ‖((2 : ℝ) ^ n) ^ 3‖ = R⁻¹ ^ 3 := by
    rw [Real.norm_of_nonneg (by positivity), hR, inv_pow, inv_pow, ← inv_pow, inv_inv]
  rw [hpow]
  calc R⁻¹ ^ 3 * ‖iteratedFDeriv ℝ k (fun v : ParabolicSpace =>
        (1 - Real.exp (R ^ 2 * v.1)) * heatShell 0 (-v)) v‖
      ≤ R⁻¹ ^ 3 * (48 * R ^ 2 * potKernelConst (heatShell 0)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = potShellConst n := by
        unfold potShellConst
        rw [← hR]
        field_simp

theorem contDiff_potShellKernel (n : ℕ) : ContDiff ℝ ∞ (potShellKernel n) :=
  (contDiff_const.sub (Real.contDiff_exp.comp (contDiff_fst.neg))).mul (contDiff_heatShell n)

/-- **The shells of `(1 - e^{-t}) G` are scaled test functions.** -/
theorem isScaledTest_potShell (n : ℕ) (z : ParabolicSpace) :
    IsScaledTest (fun y => potShellKernel n (z - y)) z ((2 : ℝ)⁻¹ ^ n) (potShellConst n) where
  contDiff := ((contDiff_potShellKernel n).comp (contDiff_const.sub contDiff_id)).of_le
    (by exact_mod_cast le_top)
  radius_pos := by positivity
  radius_le_one := pow_le_one₀ (by norm_num) (by norm_num)
  const_pos := potShellConst_pos n
  supp w hw := by
    have : heatShell n (z - w) = 0 := heatShell_eq_zero (by rwa [parabolicNorm_sub_comm])
    simp [potShellKernel, this]
  deriv k hk v := by
    have e : (fun v => (fun y => potShellKernel n (z - y)) (z + parabolicDilate ((2 : ℝ)⁻¹ ^ n) v)) =
        fun v => potShellKernel n (-(parabolicDilate ((2 : ℝ)⁻¹ ^ n) v)) := by
      funext v; simp
    rw [e]
    exact norm_iteratedFDeriv_potShell_scaled_le n hk v

end RegularityStructures.Potential

end
