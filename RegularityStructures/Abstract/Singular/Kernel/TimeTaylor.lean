/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Kernel.Shell
public import RegularityStructures.Abstract.Singular.Kernel.TimeTaylorBound
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSum

/-!
# Time-Taylor remainder of a shell derivative as a scaled test function

For `x̄ = (0, x₂)` and `0 ≤ x₁ ≤ 4^{-n}` the function
`y ↦ D^k K_n(x - y) - ∑_{j<m} x₁^j/j! D^{k + j e₀} K_n(x̄ - y)` is a scaled test function at `x`
with radius `2 · 2^{-n}` and constant `C (x₁ 4^n)^m (2^n)^{|k|_𝔰 + 3}`
(`exists_isScaledTest_shellTimeTaylorRem`), where `K_n = scaledShell h n`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `D^k K_n(x - y) - ∑_{j<m} x₁^j/j! · D^{k + j e₀} K_n((0, x₂) - y)`, `K_n = scaledShell h n`. -/
def shellTimeTaylorRem (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ) (m n : ℕ)
    (x y : ParabolicSpace) : ℝ :=
  lineIter (multiDirs k) (scaledShell h n) (x - y) - ∑ j ∈ Finset.range m,
    (x.1 ^ j / (Nat.factorial j : ℝ)) *
      lineIter (multiDirs (k + Finsupp.single 0 j)) (scaledShell h n) ((0, x.2) - y)

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

variable {N : ℕ}

theorem multiDeg_add_single_zero (k : Fin 4 →₀ ℕ) (j : ℕ) :
    multiDeg (k + Finsupp.single 0 j) = multiDeg k + 2 * j := by
  simp [multiDeg, map_add, Finsupp.weight_apply, Finsupp.sum_single_index, parabolicWeight,
    mul_comm]

theorem norm_iteratedFDeriv_comp_affine_le {Q : ParabolicSpace → ℝ}
    (hQ : ContDiff ℝ ∞ Q) {D : ℝ} (hD : ∀ k ≤ 4, ∀ u, ‖iteratedFDeriv ℝ k Q u‖ ≤ D)
    (a : ParabolicSpace) (L : ParabolicSpace →L[ℝ] ParabolicSpace) (hL : ‖L‖ ≤ 4) {i : ℕ}
    (hi : i ≤ 4) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ i (fun v => Q (a + L v)) v‖ ≤ D * 256 := by
  have hh' : ContDiff ℝ ∞ (fun u => Q (a + u)) := hQ.comp (contDiff_const.add contDiff_id)
  have e : (fun v => Q (a + L v)) = (fun u => Q (a + u)) ∘ L := by
    funext v; simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right (n := i) _
    (hh'.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl i)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _j : Fin i, ‖L‖ ≤ 256 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖L‖ ^ i ≤ 4 ^ i := pow_le_pow_left₀ (norm_nonneg _) hL i
      _ ≤ 4 ^ 4 := pow_le_pow_right₀ (by norm_num) hi
      _ = 256 := by norm_num
  have hd : ‖iteratedFDeriv ℝ i (fun u => Q (a + u)) (L v)‖ ≤ D := by
    rw [iteratedFDeriv_comp_add_left]
    exact hD i hi _
  exact mul_le_mul hd hp (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    ((norm_nonneg _).trans hd)

/-- Reduction of the remainder to the unscaled time-Taylor remainder of `D^k h`. -/
theorem shellTimeTaylorRem_eq {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) (k : Fin 4 →₀ ℕ)
    (m n : ℕ) (x y : ParabolicSpace) :
    shellTimeTaylorRem h k m n x y = ((2 : ℝ) ^ n) ^ (multiDeg k + 3) *
      timeTaylorRem (x.1 * 4 ^ n) m (lineIter (multiDirs k) h)
        (parabolicDilate (2 ^ n) ((0, x.2) - y)) := by
  set g := lineIter (multiDirs k) h with hg
  have hS : ContDiff ℝ ∞ h := hh
  unfold shellTimeTaylorRem timeTaylorRem
  have e0 : x - y = ((0, x.2) - y) + x.1 • timeDir := by
    ext
    · simp [timeDir]; ring
    · simp [timeDir]
  have h4 : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e1 : parabolicDilate (2 ^ n) (x - y) = parabolicDilate (2 ^ n) ((0, x.2) - y) +
      (x.1 * 4 ^ n) • timeDir := by
    rw [e0]
    simp only [parabolicDilate, timeDir, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero,
      smul_eq_mul, mul_one]
    ext
    · simp only [Prod.fst_add]; linear_combination x.1 * h4
    · simp
  rw [lineIter_multiDirs_scaledShell_apply hh, e1, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lineIter_multiDirs_scaledShell_apply hh, multiDeg_add_single_zero,
    lineIter_multiDirs_add_single hh k 0 j, coordDir_zero]
  have : ((2 : ℝ) ^ n) ^ (multiDeg k + 2 * j + 3) = ((2 : ℝ) ^ n) ^ (multiDeg k + 3) *
      (4 ^ n) ^ j := by
    rw [show multiDeg k + 2 * j + 3 = (multiDeg k + 3) + 2 * j by ring, pow_add, pow_mul, h4]
  rw [this, mul_pow]
  ring

end RegularityStructures

end
