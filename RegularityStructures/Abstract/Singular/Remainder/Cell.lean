/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Decay
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Analysis.Parabolic.Lattice.Cell
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Cutting a smooth function by a level-3 lattice cell

For `F` smooth with derivatives of order `≤ 4` bounded by `B` on the parabolic unit ball around
the lattice point `z_j = latticePoint 3 j` (in the coordinates `v ↦ F(z_j + v)`), the function
`F χ_{3,j}` is smooth, supported in `B(z_j, 1)`, and its scaled derivatives (radius `1`) are
bounded by `Cc B` with an absolute constant `Cc` (`exists_cell_mul_scaled_bound`).
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

private theorem norm_iteratedFDeriv_comp_dilate_eight_le {h : ParabolicSpace → ℝ}
    (hh : ContDiff ℝ ∞ h) {A : ℝ} (hA : ∀ k ≤ 4, ∀ u, ‖iteratedFDeriv ℝ k h u‖ ≤ A) {k : ℕ}
    (hk : k ≤ 4) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ k (fun v => h (parabolicDilateCLM 8 v)) v‖ ≤ A * 64 ^ 4 := by
  have e : (fun v => h (parabolicDilateCLM 8 v)) = h ∘ (parabolicDilateCLM 8) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) _
    (hh.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn : ‖parabolicDilateCLM (8 : ℝ)‖ ≤ 64 := by
    have := norm_parabolicDilateCLM_le (d := 8) (by norm_num)
    linarith
  have hp : ∏ _i : Fin k, ‖parabolicDilateCLM (8 : ℝ)‖ ≤ 64 ^ 4 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (pow_le_pow_left₀ (norm_nonneg _) hn k).trans (pow_le_pow_right₀ (by norm_num) hk)
  have hd := hA k hk (parabolicDilateCLM 8 v)
  exact mul_le_mul hd hp (Finset.prod_nonneg fun _ _ => norm_nonneg _) ((norm_nonneg _).trans hd)

private theorem two_pow_three_eq : ((2 : ℝ) ^ 3) = 8 := by norm_num

/-- Scaled derivatives of the level-3 cell `χ_{3,j}`. -/
theorem exists_cell_scaled_bound :
    ∃ Bχ : ℝ, 0 ≤ Bχ ∧ ∀ (j : LatticeIndex), ∀ k ≤ 4, ∀ v : ParabolicSpace,
      ‖iteratedFDeriv ℝ k (fun v => latticeCell 3 j (latticePoint 3 j + v)) v‖ ≤ Bχ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_iteratedFDeriv_latticeBump4 4
  refine ⟨C * 64 ^ 4, by positivity, fun j k hk v => ?_⟩
  have e : (fun v => latticeCell 3 j (latticePoint 3 j + v)) =
      fun v => latticeBump4 (parabolicDilateCLM 8 v) := by
    funext v
    have := latticeCell_latticePoint_add 3 j (parabolicDilate 8 v)
    rw [two_pow_three_eq] at this
    simp only [parabolicDilateCLM_apply]
    rw [← this]
    congr 2
    rw [show ((8 : ℝ)) = ((8 : ℝ)⁻¹)⁻¹ by norm_num]
    simpa using (parabolicDilate_inv_parabolicDilate (c := 8) (by norm_num) v).symm
  rw [e]
  exact norm_iteratedFDeriv_comp_dilate_eight_le contDiff_latticeBump4 hC hk v

theorem latticeCell_eq_zero_of_one_lt {j : LatticeIndex} {w : ParabolicSpace}
    (hw : 1 < parabolicNorm (w - latticePoint 3 j)) : latticeCell 3 j w = 0 := by
  by_contra h
  have := parabolicNorm_sub_latticePoint_le h
  norm_num at this
  linarith

/-- A smooth function with bounded scaled derivatives on the unit ball, cut by a level-3 cell. -/
theorem exists_cell_mul_scaled_bound :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (j : LatticeIndex) {F : ParabolicSpace → ℝ} {B : ℝ},
      ContDiff ℝ ∞ F → 0 ≤ B →
      (∀ i ≤ 4, ∀ v : ParabolicSpace, parabolicNorm v ≤ 1 →
        ‖iteratedFDeriv ℝ i (fun v => F (latticePoint 3 j + v)) v‖ ≤ B) →
      ContDiff ℝ ∞ (fun w => F w * latticeCell 3 j w) ∧
      (∀ w, 1 < parabolicNorm (w - latticePoint 3 j) → F w * latticeCell 3 j w = 0) ∧
      ∀ k ≤ 4, ∀ v : ParabolicSpace,
        ‖iteratedFDeriv ℝ k (fun v => (fun w => F w * latticeCell 3 j w) (latticePoint 3 j + v)) v‖
          ≤ Cc * B := by
  obtain ⟨Bχ, hBχ0, hBχ⟩ := exists_cell_scaled_bound
  refine ⟨16 * Bχ, by positivity, fun j {F B} hF hB hFB => ⟨hF.mul (contDiff_latticeCell 3 j),
    fun w hw => by rw [latticeCell_eq_zero_of_one_lt hw, mul_zero], fun k hk v => ?_⟩⟩
  have hFs : ContDiff ℝ ∞ (fun v => F (latticePoint 3 j + v)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have hχs : ContDiff ℝ ∞ (fun v => latticeCell 3 j (latticePoint 3 j + v)) :=
    (contDiff_latticeCell 3 j).comp (contDiff_const.add contDiff_id)
  by_cases hv : parabolicNorm v ≤ 1
  · refine (norm_iteratedFDeriv_mul_le hFs hχs v (n := k) (by exact_mod_cast le_top)).trans ?_
    have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun v => F (latticePoint 3 j + v)) v‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun v => latticeCell 3 j (latticePoint 3 j + v)) v‖ ≤
        (k.choose i : ℝ) * (B * Bχ) := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hFB i (hik.trans hk) v hv)
        (hBχ j _ ((Nat.sub_le _ _).trans hk) v) (norm_nonneg _) hB) (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    have h2k : (2 : ℝ) ^ k ≤ 16 := by
      calc (2 : ℝ) ^ k ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hk
        _ = 16 := by norm_num
    rw [hsum]
    have hBB : 0 ≤ B * Bχ := mul_nonneg hB hBχ0
    calc (2 : ℝ) ^ k * (B * Bχ) ≤ 16 * (B * Bχ) := mul_le_mul_of_nonneg_right h2k hBB
      _ = _ := by ring
  · push Not at hv
    have hev : (fun v => (fun w => F w * latticeCell 3 j w) (latticePoint 3 j + v)) =ᶠ[𝓝 v]
        fun _ => (0 : ℝ) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds
        (isOpen_lt continuous_const continuous_parabolicNorm :
          IsOpen {u : ParabolicSpace | 1 < parabolicNorm u}) hv) fun u hu => ?_
      have : latticeCell 3 j (latticePoint 3 j + u) = 0 :=
        latticeCell_eq_zero_of_one_lt (by simpa using hu)
      simp [this]
    rw [(hev.iteratedFDeriv ℝ k).self_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity

end RegularityStructures

end
