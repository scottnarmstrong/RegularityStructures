/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Kernel.TimeTaylor

/-!
# The time-Taylor remainder of a shell derivative is a scaled test function

`exists_isScaledTest_shellTimeTaylorRem`: for `1 ≤ n` and `0 ≤ x₁ ≤ (2^{-n})²`, the function
`shellTimeTaylorRem h k m n x` is a scaled test function at `x` with radius `2 · 2^{-n}` and
any constant `A ≥ C (x₁ 4^n)^m (2^n)^{|k|_𝔰 + 3}`.  (For `n = 0` the radius exceeds `1`, so
`n ≥ 1` is needed; for `x₁ = 0`, `m ≥ 1`, the remainder vanishes and the constant must be
allowed to be any positive number.)
-/

public section

open scoped ContDiff

namespace RegularityStructures

variable {N : ℕ}

theorem contDiff_timeTaylorRem {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g) (τ : ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (timeTaylorRem τ m g) := by
  unfold timeTaylorRem
  exact (hg.comp (contDiff_id.add contDiff_const)).sub
    (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_iterate_dirDeriv hg timeDir j))

theorem norm_projection_sub_le {x : ParabolicSpace} {n : ℕ} (hx0 : 0 ≤ x.1)
    (hx1 : x.1 ≤ (((2 : ℝ) ^ n)⁻¹) ^ 2) : parabolicNorm (((0 : ℝ), x.2) - x) ≤ ((2 : ℝ) ^ n)⁻¹ := by
  unfold parabolicNorm
  simp only [Prod.fst_sub, Prod.snd_sub, zero_sub, abs_neg, sub_self, abs_zero,
    Finset.sum_const_zero, add_zero, Pi.sub_apply]
  rw [abs_of_nonneg hx0]
  exact Real.sqrt_le_iff.2 ⟨by positivity, hx1⟩

theorem shellTimeTaylorRem_eq_zero_of_lt {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
    (k : Fin 4 →₀ ℕ) (m n : ℕ) {x y : ParabolicSpace} (hx0 : 0 ≤ x.1)
    (hx1 : x.1 ≤ (((2 : ℝ) ^ n)⁻¹) ^ 2) (hy : 2 * ((2 : ℝ) ^ n)⁻¹ < parabolicNorm (y - x)) :
    shellTimeTaylorRem h k m n x y = 0 := by
  have hq : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have h1 : ((2 : ℝ) ^ n)⁻¹ < parabolicNorm (x - y) := by
    rw [parabolicNorm_sub_comm]; linarith
  have h2 : ((2 : ℝ) ^ n)⁻¹ < parabolicNorm (((0 : ℝ), x.2) - y) := by
    have e : y - x = (y - ((0 : ℝ), x.2)) + (((0 : ℝ), x.2) - x) := by abel
    have := parabolicNorm_add_le (y - ((0 : ℝ), x.2)) (((0 : ℝ), x.2) - x)
    rw [← e] at this
    rw [parabolicNorm_sub_comm]
    linarith [norm_projection_sub_le hx0 hx1]
  unfold shellTimeTaylorRem
  rw [lineIter_multiDirs_scaledShell_eq_zero_of_lt hh k n h1, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [lineIter_multiDirs_scaledShell_eq_zero_of_lt hh _ n h2, mul_zero]

theorem contDiff_shellTimeTaylorRem {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h)
    (k : Fin 4 →₀ ℕ) (m n : ℕ) (x : ParabolicSpace) :
    ContDiff ℝ ∞ (shellTimeTaylorRem h k m n x) := by
  have hs := contDiff_scaledShell hh n
  unfold shellTimeTaylorRem
  refine (contDiff_lineIter hs _ |>.comp (contDiff_const.sub contDiff_id)).sub
    (ContDiff.sum fun j _ => contDiff_const.mul
      ((contDiff_lineIter hs _).comp (contDiff_const.sub contDiff_id)))

/-- Scaling of the argument in the profile of `shellTimeTaylorRem`. -/
theorem parabolicDilate_projection_sub (n : ℕ) (x v : ParabolicSpace) :
    parabolicDilate ((2 : ℝ) ^ n) (((0 : ℝ), x.2) - (x + parabolicDilate (2 * ((2 : ℝ) ^ n)⁻¹) v))
      = (-(x.1 * 4 ^ n)) • timeDir + (-(parabolicDilateCLM 2)) v := by
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have h4 : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hR : (2 : ℝ) ^ n * (2 * ((2 : ℝ) ^ n)⁻¹) = 2 := by field_simp
  have hR2 : ((2 : ℝ) ^ n) ^ 2 * (2 * ((2 : ℝ) ^ n)⁻¹) ^ 2 = 4 := by
    rw [← mul_pow, hR]; norm_num
  ext
  · simp only [parabolicDilate, timeDir, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
      zero_sub, neg_apply, parabolicDilateCLM_apply, Prod.fst_neg]
    linear_combination (-x.1) * h4 - v.1 * hR2
  · rename_i i
    simp only [parabolicDilate, timeDir, Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_zero,
      neg_apply, parabolicDilateCLM_apply, Prod.snd_neg, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.zero_apply, zero_add]
    linear_combination (-v.2 i) * hR

private theorem norm_neg_parabolicDilateCLM_two_le : ‖-(parabolicDilateCLM 2)‖ ≤ 4 := by
  rw [norm_neg]
  have := norm_parabolicDilateCLM_le (d := 2) (by norm_num)
  linarith

theorem exists_isScaledTest_shellTimeTaylorRem {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
    (k : Fin 4 →₀ ℕ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ParabolicSpace, 0 ≤ x.1 →
      x.1 ≤ (((2 : ℝ) ^ n)⁻¹) ^ 2 → ∀ A : ℝ, 0 < A →
      C * (x.1 * 4 ^ n) ^ m * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3) ≤ A →
      IsScaledTest (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y) -
          ∑ j ∈ Finset.range m, (x.1 ^ j / (Nat.factorial j : ℝ)) *
            lineIter (multiDirs (k + Finsupp.single 0 j)) (scaledShell h n) ((0, x.2) - y))
        x (2 * ((2 : ℝ) ^ n)⁻¹) A := by
  have hgs : ContDiff ℝ ∞ (lineIter (multiDirs k) h) := contDiff_lineIter hh.contDiff _
  have hgc : HasCompactSupport (lineIter (multiDirs k) h) :=
    hasCompactSupport_of_eq_zero_unit fun w hw => lineIter_eq_zero_of_lt hh.eq_zero _ hw
  obtain ⟨B, hB0, hB⟩ := exists_norm_iteratedFDeriv_timeTaylorRem_le hgs hgc m
  refine ⟨(B + 1) * 256, by positivity, fun n hn x hx0 hx1 A hA hCA => ?_⟩
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have h2n : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hq : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have hq1 : 2 * ((2 : ℝ) ^ n)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hc]
    linarith
  have h4 : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hτ : 0 ≤ x.1 * 4 ^ n := by positivity
  refine ⟨contDiff_shellTimeTaylorRem hh.contDiff k m n x, by positivity, hq1, hA,
    fun y hy => shellTimeTaylorRem_eq_zero_of_lt hh k m n hx0 hx1 hy, fun i hi v => ?_⟩
  set Q := timeTaylorRem (x.1 * 4 ^ n) m (lineIter (multiDirs k) h) with hQ
  have hQs : ContDiff ℝ ∞ Q := contDiff_timeTaylorRem hgs _ _
  have e : (fun v => shellTimeTaylorRem h k m n x (x + parabolicDilate (2 * ((2 : ℝ) ^ n)⁻¹) v)) =
      ((2 : ℝ) ^ n) ^ (multiDeg k + 3) •
        fun v => Q ((-(x.1 * 4 ^ n)) • timeDir + (-(parabolicDilateCLM 2)) v) := by
    funext v
    rw [shellTimeTaylorRem_eq hh.contDiff, parabolicDilate_projection_sub]
    rfl
  have hQa : ContDiff ℝ ∞ (fun v => Q ((-(x.1 * 4 ^ n)) • timeDir + (-(parabolicDilateCLM 2)) v)) :=
    hQs.comp (contDiff_const.add (-(parabolicDilateCLM 2)).contDiff)
  have hD := norm_iteratedFDeriv_comp_affine_le hQs (D := B * |x.1 * 4 ^ n| ^ m)
    (fun j hj u => hB _ j hj u) ((-(x.1 * 4 ^ n)) • timeDir) (-(parabolicDilateCLM 2))
    norm_neg_parabolicDilateCLM_two_le hi v
  change ‖iteratedFDeriv ℝ i (fun v => shellTimeTaylorRem h k m n x
    (x + parabolicDilate (2 * ((2 : ℝ) ^ n)⁻¹) v)) v‖ ≤ A
  rw [e, iteratedFDeriv_const_smul_apply (hQa.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [abs_of_nonneg hτ] at hD
  rw [two_pow_rpow_multiDeg_add_three] at hCA
  have ht : 0 ≤ (x.1 * 4 ^ n) ^ m := by positivity
  have hc0 : 0 ≤ ((2 : ℝ) ^ n) ^ (multiDeg k + 3) := by positivity
  calc _ ≤ ((2 : ℝ) ^ n) ^ (multiDeg k + 3) * (B * (x.1 * 4 ^ n) ^ m * 256) :=
        mul_le_mul_of_nonneg_left hD hc0
    _ ≤ A := by nlinarith [mul_nonneg ht hc0]

end RegularityStructures

end
