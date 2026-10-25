/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Analysis.Heat.Causal.Support
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral

/-!
# Shell derivatives as scaled test functions

For a shell profile `h` and a multi-index `k`, the function
`y ↦ D^k (scaledShell h n) (x - y)` is a scaled test function at `x` with radius `2^{-n}` and
constant `C (2^n)^{|k|_𝔰 + 3}` (`exists_isScaledTest_lineIter_multiDirs_scaledShell`), and it is
causal if the profile is (`lineIter_multiDirs_scaledShell_eq_zero_of_le`).
-/

public section

open scoped ContDiff

namespace RegularityStructures

variable {N : ℕ}

theorem parabolicDilate_neg (c : ℝ) (z : ParabolicSpace) :
    parabolicDilate c (-z) = -parabolicDilate c z := by
  simp [parabolicDilate]

/-- Pointwise form of the scaling of the derivatives of a dyadic shell. -/
theorem lineIter_multiDirs_scaledShell_apply {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (k : Fin 4 →₀ ℕ) (n : ℕ) (z : ParabolicSpace) :
    lineIter (multiDirs k) (scaledShell h n) z =
      ((2 : ℝ) ^ n) ^ (multiDeg k + 3) * lineIter (multiDirs k) h (parabolicDilate (2 ^ n) z) := by
  rw [lineIter_multiDirs_scaledShell h0 k n]
  simp only [scaledShell, pow_add]
  ring

theorem two_pow_rpow_multiDeg_add_three (n : ℕ) (k : Fin 4 →₀ ℕ) :
    ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3) = ((2 : ℝ) ^ n) ^ (multiDeg k + 3) := by
  have : ((multiDeg k : ℝ) + 3) = ((multiDeg k + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_natCast]

theorem lineIter_multiDirs_scaledShell_eq_zero_of_lt {h : ParabolicSpace → ℝ}
    (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) (n : ℕ) {z : ParabolicSpace}
    (hz : ((2 : ℝ) ^ n)⁻¹ < parabolicNorm z) : lineIter (multiDirs k) (scaledShell h n) z = 0 := by
  rw [lineIter_multiDirs_scaledShell_apply hh.contDiff,
    lineIter_eq_zero_of_lt hh.eq_zero _ ?_, mul_zero]
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  rw [parabolicNorm_parabolicDilate hc.le]
  exact (inv_lt_iff_one_lt_mul₀' hc).1 hz

/-- Causality of the derivatives of a causal shell. -/
theorem lineIter_scaledShell_eq_zero_of_nonpos {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h)
    (h0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (L : List ParabolicSpace) (n : ℕ)
    {z : ParabolicSpace} (hz : z.1 ≤ 0) : lineIter L (scaledShell h n) z = 0 := by
  refine lineIter_eq_zero_of_nonpos (contDiff_scaledShell hh n) (fun w hw => ?_) L hz
  have h2 : (parabolicDilate (2 ^ n) w).1 ≤ 0 := by
    simp only [parabolicDilate]
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 2 := by positivity
    nlinarith
  simp [scaledShell, h0 _ h2]

/-- `D^k (scaledShell h n) (x - y) = 0` for `x.1 ≤ y.1` if the profile is causal. -/
theorem lineIter_multiDirs_scaledShell_sub_eq_zero {h : ParabolicSpace → ℝ}
    (hh : ContDiff ℝ ∞ h) (h0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)
    (n : ℕ) {x y : ParabolicSpace} (hxy : x.1 ≤ y.1) :
    lineIter (multiDirs k) (scaledShell h n) (x - y) = 0 :=
  lineIter_scaledShell_eq_zero_of_nonpos hh h0 _ n (by simpa using hxy)

/-- Derivatives of a shell as scaled test functions: `A R⁵ = C 2^{(|k|_𝔰 - 2) n}`. -/
theorem exists_isScaledTest_lineIter_multiDirs_scaledShell {h : ParabolicSpace → ℝ}
    (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : ParabolicSpace),
      IsScaledTest (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) x
        (((2 : ℝ) ^ n)⁻¹) (C * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3)) := by
  set g := lineIter (multiDirs k) h with hg
  have hgs : ContDiff ℝ ∞ g := contDiff_lineIter hh.contDiff _
  have hg0 : ∀ w, 1 < parabolicNorm w → g w = 0 := fun w hw =>
    lineIter_eq_zero_of_lt hh.eq_zero _ hw
  have hGs : ContDiff ℝ ∞ (fun v => g (-v)) := hgs.comp contDiff_neg
  have hG0 : HasCompactSupport (fun v => g (-v)) :=
    hasCompactSupport_of_eq_zero_unit fun w hw => hg0 _ (by rwa [parabolicNorm_neg])
  obtain ⟨C₀, hC₀, hC⟩ := hG0.exists_bound_iteratedFDeriv hGs 4
  refine ⟨C₀ + 1, by linarith, fun n x => ?_⟩
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hcn : (0 : ℝ) < ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) + 3) := by positivity
  have hF : ContDiff ℝ ∞ (lineIter (multiDirs k) (scaledShell h n)) :=
    contDiff_lineIter (contDiff_scaledShell hh.contDiff n) _
  refine ⟨hF.comp (contDiff_const.sub contDiff_id), by positivity,
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)), by positivity, fun w hw => ?_, ?_⟩
  · refine lineIter_multiDirs_scaledShell_eq_zero_of_lt hh k n ?_
    rwa [parabolicNorm_sub_comm] at hw
  · intro i hi v
    have e : (fun v => lineIter (multiDirs k) (scaledShell h n)
        (x - (x + parabolicDilate ((2 : ℝ) ^ n)⁻¹ v))) =
        ((2 : ℝ) ^ n) ^ (multiDeg k + 3) • fun v => g (-v) := by
      funext v
      rw [lineIter_multiDirs_scaledShell_apply hh.contDiff, sub_add_cancel_left,
        parabolicDilate_neg, parabolicDilate_parabolicDilate_inv hc.ne']
      rfl
    rw [e, iteratedFDeriv_const_smul_apply (hGs.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, two_pow_rpow_multiDeg_add_three, Real.norm_of_nonneg (by positivity)]
    rw [mul_comm (C₀ + 1)]
    exact mul_le_mul_of_nonneg_left ((hC i hi v).trans (by linarith)) (by positivity)

end RegularityStructures

end
