/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.ShellTest
public import Phi43.Potential.PairingSum
public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Decomposition.Basic

/-!
# The singular part `∑_{n ≥ n₀} (1 - e^{-t}) heatShell n` of `K - G^m`

`potSing n₀ w = ∑_{n ≥ n₀} potShellKernel n w` (a finite sum for `w ≠ 0`).  Paired with the noise
coordinate of degree `d > -4` it is bounded by the model constants times the geometric sum
`potSingConst d n₀ = ∑_j potShellConst (j + n₀) · R_j⁵ · R_j^d`, `R_j = 2^{-(j + n₀)}`
(`abs_potConv_potSing_le`).  The factor `(1 - e^{-t}) = O(R²)` upgrades the order of the kernel from
`2` to `4`, which makes the sum converge for the noise degree `-5/2 - κ`.
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

/-- `∑_{n ≥ n₀} (1 - e^{-w₀}) heatShell n w`. -/
@[expose] noncomputable def potSing (n₀ : ℕ) (w : ParabolicSpace) : ℝ :=
  ∑' j : ℕ, potShellKernel (j + n₀) w

/-- The geometric constant of the shell sum for a noise of degree `d`. -/
@[expose] noncomputable def potSingConst (d : ℝ) (n₀ : ℕ) : ℝ :=
  ∑' j : ℕ, potShellConst (j + n₀) * ((2 : ℝ)⁻¹ ^ (j + n₀)) ^ 5 * ((2 : ℝ)⁻¹ ^ (j + n₀)) ^ d

theorem hasSum_potShellKernel (n₀ : ℕ) (w : ParabolicSpace) :
    HasSum (fun j : ℕ => potShellKernel (j + n₀) w) (potSing n₀ w) := by
  by_cases hw : w = 0
  · subst hw
    have : ∀ j : ℕ, potShellKernel (j + n₀) 0 = 0 := fun j => by simp [potShellKernel]
    simp only [this]
    unfold potSing
    simp only [this, tsum_zero]
    exact hasSum_zero
  · obtain ⟨M, hM⟩ := exists_inv_pow_lt hw
    have hvan : ∀ j, M ≤ j + n₀ → potShellKernel (j + n₀) w = 0 := fun j hj => by
      have : heatShell (j + n₀) w = 0 := heatShell_eq_zero (lt_of_le_of_lt
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj) hM)
      simp [potShellKernel, this]
    have h : HasSum (fun j : ℕ => potShellKernel (j + n₀) w)
        (∑ j ∈ Finset.range M, potShellKernel (j + n₀) w) :=
      hasSum_sum_of_ne_finset_zero fun j hj =>
        hvan j (by have := Finset.mem_range.not.1 hj; omega)
    unfold potSing
    rw [h.tsum_eq]
    exact h

theorem potShell_term_eq (d : ℝ) (m : ℕ) :
    potShellConst m * ((2 : ℝ)⁻¹ ^ m) ^ 5 * ((2 : ℝ)⁻¹ ^ m) ^ d =
      48 * potKernelConst (heatShell 0) * ((2 : ℝ)⁻¹ ^ (4 + d)) ^ m := by
  have hR : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have h1 : ((2 : ℝ)⁻¹ ^ m) ^ (4 + d) = ((2 : ℝ)⁻¹ ^ (4 + d)) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have h2 : ((2 : ℝ)⁻¹ ^ m) ^ (4 + d) = ((2 : ℝ)⁻¹ ^ m) ^ 4 * ((2 : ℝ)⁻¹ ^ m) ^ d := by
    rw [Real.rpow_add hR]; simp
  unfold potShellConst
  rw [← h1, h2]
  field_simp

theorem summable_potSing_terms {d : ℝ} (hd : -4 < d) (n₀ : ℕ) :
    Summable fun j : ℕ => potShellConst (j + n₀) * ((2 : ℝ)⁻¹ ^ (j + n₀)) ^ 5 *
      ((2 : ℝ)⁻¹ ^ (j + n₀)) ^ d := by
  have hq0 : 0 ≤ (2 : ℝ)⁻¹ ^ (4 + d) := by positivity
  have hq1 : (2 : ℝ)⁻¹ ^ (4 + d) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  simp only [potShell_term_eq]
  have := (summable_geometric_of_lt_one hq0 hq1).mul_left
    (48 * potKernelConst (heatShell 0) * ((2 : ℝ)⁻¹ ^ (4 + d)) ^ n₀)
  refine this.congr fun j => ?_
  rw [pow_add]; ring

end RegularityStructures.Potential

end
