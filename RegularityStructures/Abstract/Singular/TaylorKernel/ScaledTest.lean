/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TaylorKernel.Scale
public import RegularityStructures.Abstract.Singular.TaylorKernel.ProfileDeriv
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Abstract.Profile.Basic

/-!
# The Taylor-remainder kernel is a scaled test function

For a shell profile `h`, `k ∈ ℕ⁴`, `σ > 0`, `n ≥ 1` and `‖y - x‖_𝔰 ≤ 2^{-n}`, the function
`w ↦ D^k K_n(y - w) - ∑_{|l|_𝔰 < σ} (y - x)^l/l! D^{k+l} K_n(x - w)` is a test function scaled at
`x` with radius `2 · 2^{-n}` and constant `C (‖y - x‖_𝔰 2^n)^σ (2^n)^{|k|_𝔰 + 3}`
(`exists_isScaledTest_dTaylorKernel`). Since `A R⁵ ≍ (‖y - x‖ 2^n)^σ 2^{(|k|_𝔰 - 2) n}`, this is
the sup-norm form of Hairer's kernel estimate.

The constant `A` of `IsScaledTest` must be positive, so the statement needs `y ≠ x` (for `y = x`
the function vanishes identically); `exists_isScaledTest_dTaylorKernel_of_le` gives the version
with an arbitrary positive constant `A` above the bound, valid also for `y = x`. The radius
`2 · 2^{-n}` is `≤ 1` only for `n ≥ 1`.

Source: [Hai14] = arXiv:1303.5113v4, (5.14), Lemma 5.18, Proposition 6.16.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem norm_parabolicDilateCLM_two_le : ‖parabolicDilateCLM 2‖ ≤ 4 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun z => ?_
  rw [parabolicDilateCLM_apply, Prod.norm_def]
  simp only [parabolicDilate]
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs, abs_mul]
    have : |(2 : ℝ) ^ 2| = 4 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact le_max_left _ _)
      (by norm_num)
  · rw [norm_smul]
    have : ‖(2 : ℝ)‖ = 2 := by norm_num
    rw [this]
    nlinarith [norm_nonneg z.2, norm_snd_le z, norm_nonneg z.1]

theorem exists_isScaledTest_dTaylorKernel_of_le {h : ParabolicSpace → ℝ} {N : ℕ}
    (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (x y : ParabolicSpace),
      parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ → ∀ A : ℝ, 0 < A →
      C * (parabolicNorm (y - x) * (2 : ℝ) ^ n) ^ σ * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3) ≤ A →
      IsScaledTest (fun w => dTaylorKernel h k n σ x y w) x (2 * ((2 : ℝ) ^ n)⁻¹) A := by
  have hcs : HasCompactSupport h :=
    HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun _ hz => hh.eq_zero _ (not_le.1 hz)
  have hGs : ContDiff ℝ ∞ (lineIter (multiDirs k) h) := contDiff_lineIter hh.contDiff _
  obtain ⟨C₁, hC₁, hb⟩ := exists_norm_iteratedFDeriv_taylorProfile_le hGs
    (hasCompactSupport_lineIter hcs _) hσ
  refine ⟨256 * C₁ + 1, by positivity, fun n hn x y hy A hA hAb => ?_⟩
  have hc : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hc2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  set s : ParabolicSpace := parabolicDilate ((2 : ℝ) ^ n) (y - x) with hs
  have hsn : parabolicNorm s = parabolicNorm (y - x) * (2 : ℝ) ^ n := by
    rw [hs, parabolicNorm_parabolicDilate hc.le, mul_comm]
  have hs1 : parabolicNorm s ≤ 1 := by
    rw [hsn]
    calc parabolicNorm (y - x) * (2 : ℝ) ^ n ≤ ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hy hc.le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  set R : ℝ := 2 * ((2 : ℝ) ^ n)⁻¹ with hR
  have hRc : (2 : ℝ) ^ n * R = 2 := by rw [hR]; field_simp
  have hcoeff : ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3) = ((2 : ℝ) ^ n) ^ (3 + multiDeg k) := by
    rw [show ((multiDeg k : ℝ) + 3) = ((3 + multiDeg k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hcoeff, ← hsn] at hAb
  have hc0 : (0 : ℝ) < ((2 : ℝ) ^ n) ^ (3 + multiDeg k) := by positivity
  have hP : ∀ (v : ParabolicSpace), dTaylorKernel h k n σ x y (x + parabolicDilate R v) =
      ((2 : ℝ) ^ n) ^ (3 + multiDeg k) *
        taylorProfile (lineIter (multiDirs k) h) σ s (-(parabolicDilateCLM 2) v) := by
    intro v
    have e1 : parabolicDilate ((2 : ℝ) ^ n) (x - (x + parabolicDilate R v)) =
        -(parabolicDilateCLM 2 v) := by
      rw [show x - (x + parabolicDilate R v) = -(parabolicDilate R v) by abel,
        ← parabolicDilateCLM_apply, map_neg, parabolicDilateCLM_apply, ← parabolicDilate_mul,
        hRc, parabolicDilateCLM_apply]
    rw [dTaylorKernel_eq_profile hh.contDiff, e1]
  refine ⟨?_, by positivity, by nlinarith [pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn], hA, ?_, ?_⟩
  · have : (fun w => dTaylorKernel h k n σ x y w) = fun w => ((2 : ℝ) ^ n) ^ (3 + multiDeg k) *
        taylorProfile (lineIter (multiDirs k) h) σ s (parabolicDilate (2 ^ n) (x - w)) := by
      funext w; exact dTaylorKernel_eq_profile hh.contDiff k n σ x y w
    rw [this]
    refine contDiff_const.mul ((contDiff_taylorProfile hGs σ s).comp ?_)
    exact ((parabolicDilateCLM ((2 : ℝ) ^ n)).contDiff).comp (contDiff_const.sub contDiff_id)
  · intro w hw
    exact dTaylorKernel_eq_zero hh.contDiff hh.eq_zero k n σ hy hw
  · intro j hj v
    have e : (fun v => dTaylorKernel h k n σ x y (x + parabolicDilate R v)) =
        ((2 : ℝ) ^ n) ^ (3 + multiDeg k) • (taylorProfile (lineIter (multiDirs k) h) σ s ∘
          (-(parabolicDilateCLM 2))) := by
      funext v; rw [hP]; rfl
    rw [e]
    have hPs := contDiff_taylorProfile hGs σ s
    rw [iteratedFDeriv_const_smul_apply ((hPs.comp (-(parabolicDilateCLM 2)).contDiff).of_le
      (by exact_mod_cast le_top) : ContDiff ℝ j _).contDiffAt, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc0]
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right (n := j) _ (hPs.of_le (by exact_mod_cast le_top)) _
      (by exact_mod_cast le_refl j)]
    have hL : ‖-(parabolicDilateCLM 2)‖ ≤ 4 := by rw [norm_neg]; exact norm_parabolicDilateCLM_two_le
    have hprod : ∏ _i : Fin j, ‖-(parabolicDilateCLM 2)‖ ≤ 4 ^ 4 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc ‖-(parabolicDilateCLM 2)‖ ^ j ≤ 4 ^ j := pow_le_pow_left₀ (norm_nonneg _) hL _
        _ ≤ 4 ^ 4 := pow_le_pow_right₀ (by norm_num) hj
    have h1 : ‖(iteratedFDeriv ℝ j (taylorProfile (lineIter (multiDirs k) h) σ s)
        (-(parabolicDilateCLM 2) v)).compContinuousLinearMap fun _ => -(parabolicDilateCLM 2)‖ ≤
        ‖iteratedFDeriv ℝ j (taylorProfile (lineIter (multiDirs k) h) σ s)
          (-(parabolicDilateCLM 2) v)‖ * 4 ^ 4 :=
      (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
    have h2 := hb s hs1 j hj (-(parabolicDilateCLM 2) v)
    have hd0 : 0 ≤ parabolicNorm s ^ σ := Real.rpow_nonneg (parabolicNorm_nonneg _) _
    calc ((2 : ℝ) ^ n) ^ (3 + multiDeg k) * ‖(iteratedFDeriv ℝ j (taylorProfile
          (lineIter (multiDirs k) h) σ s) (-(parabolicDilateCLM 2) v)).compContinuousLinearMap
          fun _ => -(parabolicDilateCLM 2)‖
        ≤ ((2 : ℝ) ^ n) ^ (3 + multiDeg k) * (256 * C₁ * parabolicNorm s ^ σ) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) hc0.le
          calc _ ≤ (C₁ * parabolicNorm s ^ σ) * 4 ^ 4 :=
                mul_le_mul_of_nonneg_right h2 (by norm_num)
            _ = _ := by ring
      _ ≤ ((2 : ℝ) ^ n) ^ (3 + multiDeg k) * ((256 * C₁ + 1) * parabolicNorm s ^ σ) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0.le
          nlinarith
      _ = (256 * C₁ + 1) * parabolicNorm s ^ σ * ((2 : ℝ) ^ n) ^ (3 + multiDeg k) := by ring
      _ ≤ A := hAb

/-- `D^k K_n(y - w) - ∑_{|l|_𝔰 < σ} (y - x)^l/l! D^{k+l} K_n(x - w)` is a test function scaled at
`x` with radius `2 · 2^{-n}` and constant `C (‖y - x‖ 2^n)^σ (2^n)^{|k|_𝔰 + 3}`, for `n ≥ 1`,
`0 < ‖y - x‖_𝔰 ≤ 2^{-n}`. -/
theorem exists_isScaledTest_dTaylorKernel {h : ParabolicSpace → ℝ} {N : ℕ}
    (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (x y : ParabolicSpace), 0 < parabolicNorm (y - x) →
      parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ →
      IsScaledTest (fun w => dTaylorKernel h k n σ x y w) x (2 * ((2 : ℝ) ^ n)⁻¹)
        (C * (parabolicNorm (y - x) * (2 : ℝ) ^ n) ^ σ *
          ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3)) := by
  obtain ⟨C, hC, H⟩ := exists_isScaledTest_dTaylorKernel_of_le hh k hσ
  refine ⟨C, hC, fun n hn x y hxy hy => H n hn x y hy _ ?_ le_rfl⟩
  have hc : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have : 0 < parabolicNorm (y - x) * (2 : ℝ) ^ n := mul_pos hxy hc
  positivity

end RegularityStructures

end
