/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.Kernel1Estimate
public import RegularityStructures.Analysis.Heat.Decomposition.Basic

/-!
# The decomposition of the singular kernel `K`

For `w ≠ 0`:  `K(w) = (1 - χ(w₀)) K(w) + χ(w₀) e^{-w₀} G(w) + potK1 N w`, i.e.

`K = potTail N + (χ G^m) + potK1 N`  with `G^m = e^{-t} G` the massive Euclidean heat kernel
(`hairerKernel_eq_decomp`), because `potK1 N = χ (K - e^{-t} G)` (`potK1_eq`).
-/

public section

open Filter Topology Set

namespace RegularityStructures.Potential

theorem summable_heatShell (w : ParabolicSpace) (hw : w ≠ 0) :
    Summable fun n : ℕ => heatShell n w := by
  obtain ⟨M, hM⟩ := exists_inv_pow_lt hw
  refine summable_of_ne_finset_zero (s := Finset.range M) fun n hn => ?_
  have : M ≤ n := by simpa using hn
  exact heatShell_eq_zero (lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) this) hM)

theorem potCutoff_mul_potSing (w : ParabolicSpace) :
    potCutoff w.1 * potSing 2 w = potSing 2 w := by
  by_cases h : w.1 ≤ 1 / 8
  · rw [potCutoff_eq_one h, one_mul]
  · push Not at h
    have hz : ∀ j : ℕ, potShellKernel (j + 2) w = 0 := fun j => by
      have h1 : heatShell (j + 2) w = 0 := by
        refine heatShell_eq_zero ?_
        have h2 : Real.sqrt (1 / 8) ≤ Real.sqrt |w.1| :=
          Real.sqrt_le_sqrt (by rw [abs_of_pos (by linarith)]; exact h.le)
        have h3 : Real.sqrt |w.1| ≤ parabolicNorm w := by
          unfold parabolicNorm
          have := Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
            abs_nonneg (w.2 i)
          linarith
        have h4 : (1 / 4 : ℝ) < Real.sqrt (1 / 8) := by
          rw [Real.lt_sqrt (by norm_num)]; norm_num
        have h5 : (2 : ℝ)⁻¹ ^ (j + 2) ≤ 1 / 4 := by
          calc (2 : ℝ)⁻¹ ^ (j + 2) ≤ (2 : ℝ)⁻¹ ^ 2 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 4 := by norm_num
        linarith
      simp [potShellKernel, h1]
    have : potSing 2 w = 0 := by
      unfold potSing; simp [hz]
    rw [this, mul_zero]

theorem potK1_eq (N : ℕ) {w : ParabolicSpace} (hw : w ≠ 0) :
    potK1 N w = potCutoff w.1 * (Phi43.hairerKernel N w - Real.exp (-w.1) * heatKernelR4 w) := by
  have hK := Phi43.hairerKernel_eq_heat_sub_remainder (N := N) hw
  have hG := heatKernelR4_eq_tsum hw
  have hsum := summable_heatShell w hw
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hsing : potSing 2 w = (1 - Real.exp (-w.1)) * ∑' j : ℕ, heatShell (j + 2) w := by
    unfold potSing potShellKernel
    rw [tsum_mul_left]
  have hχ := potCutoff_mul_potSing w
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
  unfold potK1 potUnit potUnitBump potTailPhi potShellKernel
  unfold annRemainderC at *
  rw [hK, hG, ← hsplit]
  rw [hsing] at hχ ⊢
  set e := Real.exp (-w.1)
  set c := potCutoff w.1
  set S := ∑' j : ℕ, heatShell (j + 2) w
  have : c * ((1 - e) * S) = (1 - e) * S := hχ
  nlinarith [this]

end RegularityStructures.Potential

end
