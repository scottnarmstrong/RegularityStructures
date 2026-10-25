/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Decay
public import RegularityStructures.Analysis.Parabolic.Lattice.Cell
public import Mathlib.Analysis.PSeries

/-!
# Summation of the spatial weights over the level-3 lattice

`remCellWt x j = (1 + |x' − z_j'|²)^{-3}` for `j` in the time window `-1 ≤ j₀ ≤ 63` (and `0`
otherwise) is summable over `LatticeIndex`, with a bound `∑ ≤ W` independent of `x`
(`summable_remCellWt`, `tsum_remCellWt_le`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The weight of the level-3 cell `j` seen from `x`, supported on the time window
`-1 ≤ j₀ ≤ 63`. -/
def remCellWt (x : ParabolicSpace) (j : LatticeIndex) : ℝ :=
  if j.1 ∈ Finset.Icc (-1 : ℤ) 63 then remWt (x.2 - (latticePoint 3 j).2) else 0

end RegularityStructures

end

public section

open Filter

namespace RegularityStructures

theorem remCellWt_nonneg (x : ParabolicSpace) (j : LatticeIndex) : 0 ≤ remCellWt x j := by
  unfold remCellWt; split_ifs
  · exact remWt_nonneg _
  · exact le_rfl

private theorem summable_aux : Summable (fun N : ℤ => (1 + (N : ℝ) ^ 2 / 256)⁻¹) := by
  refine Summable.of_norm_bounded_eventually (g := fun N : ℤ => 256 * (1 / (N : ℝ) ^ 2))
    ((Real.summable_one_div_int_pow.2 (by norm_num)).mul_left 256) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by
    intro h; exact hN (by simpa using (Int.cast_eq_zero.1 h))
  have hN2 : 0 < (N : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), mul_one_div, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) hN2]
  nlinarith

private theorem term_le (a : ℝ) (n : ℤ) :
    (1 + (a - (8 : ℝ)⁻¹ * n) ^ 2)⁻¹ ≤ 2 * (1 + ((n - ⌊8 * a⌋ : ℤ) : ℝ) ^ 2 / 256)⁻¹ := by
  set r : ℝ := 8 * a - ⌊8 * a⌋ with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith [Int.floor_le (8 * a)]
  have hr1 : r < 1 := by rw [hr]; linarith [Int.lt_floor_add_one (8 * a)]
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  set N : ℝ := ((n - ⌊8 * a⌋ : ℤ) : ℝ) with hN
  have e : a - (8 : ℝ)⁻¹ * n = (r - N) / 8 := by
    rw [hN, hr]; push_cast; ring
  rw [e]
  have hX : 0 < 1 + ((r - N) / 8) ^ 2 := by positivity
  have hY : 0 < 1 + N ^ 2 / 256 := by positivity
  have key : 1 + N ^ 2 / 256 ≤ 2 * (1 + ((r - N) / 8) ^ 2) := by
    nlinarith [sq_nonneg (N - 2 * r)]
  calc (1 + ((r - N) / 8) ^ 2)⁻¹ = 1 / (1 + ((r - N) / 8) ^ 2) := by rw [one_div]
    _ ≤ 2 / (1 + N ^ 2 / 256) := by rw [div_le_div_iff₀ hX hY]; linarith
    _ = 2 * (1 + N ^ 2 / 256)⁻¹ := by rw [div_eq_mul_inv]

/-- One-dimensional lattice sums of the weight are bounded uniformly in the shift. -/
theorem exists_sum_inv_one_add_sq_le :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (a : ℝ) (S : Finset ℤ),
      ∑ n ∈ S, (1 + (a - (8 : ℝ)⁻¹ * n) ^ 2)⁻¹ ≤ H := by
  refine ⟨2 * ∑' N : ℤ, (1 + (N : ℝ) ^ 2 / 256)⁻¹, ?_, fun a S => ?_⟩
  · exact mul_nonneg zero_le_two (tsum_nonneg fun N => by positivity)
  · calc ∑ n ∈ S, (1 + (a - (8 : ℝ)⁻¹ * n) ^ 2)⁻¹
        ≤ ∑ n ∈ S, 2 * (1 + ((n - ⌊8 * a⌋ : ℤ) : ℝ) ^ 2 / 256)⁻¹ :=
          Finset.sum_le_sum fun n _ => term_le a n
      _ = 2 * ∑ n ∈ S, (1 + ((n - ⌊8 * a⌋ : ℤ) : ℝ) ^ 2 / 256)⁻¹ := by rw [Finset.mul_sum]
      _ = 2 * ∑ N ∈ S.image (fun n : ℤ => n - ⌊8 * a⌋), (1 + (N : ℝ) ^ 2 / 256)⁻¹ := by
          rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
      _ ≤ 2 * ∑' N : ℤ, (1 + (N : ℝ) ^ 2 / 256)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_two
          exact summable_aux.sum_le_tsum _ (fun N _ => by positivity)

theorem remWt_le_prod (a : Fin 3 → ℝ) : remWt a ≤ ∏ i, (1 + a i ^ 2)⁻¹ := by
  have hS := sqNorm3_nonneg a
  have h1 : ∏ i, (1 + a i ^ 2) ≤ (1 + sqNorm3 a) ^ 3 := by
    have : ∀ i : Fin 3, 1 + a i ^ 2 ≤ 1 + sqNorm3 a := fun i => by
      have := Finset.single_le_sum (f := fun j => a j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
      unfold sqNorm3; linarith
    calc ∏ i, (1 + a i ^ 2) ≤ ∏ _i : Fin 3, (1 + sqNorm3 a) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => this i
      _ = (1 + sqNorm3 a) ^ 3 := by simp
  unfold remWt
  rw [inv_pow, Finset.prod_inv_distrib]
  exact inv_anti₀ (Finset.prod_pos fun i _ => by positivity) h1

/-- Three-dimensional lattice sums of the weight are bounded uniformly in the shift. -/
theorem exists_sum_remWt_le :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (b : Fin 3 → ℝ) (S : Finset (Fin 3 → ℤ)),
      ∑ p ∈ S, remWt (fun i => b i - (8 : ℝ)⁻¹ * p i) ≤ H := by
  classical
  obtain ⟨H, hH0, hH⟩ := exists_sum_inv_one_add_sq_le
  refine ⟨H ^ 3, by positivity, fun b S => ?_⟩
  calc ∑ p ∈ S, remWt (fun i => b i - (8 : ℝ)⁻¹ * p i)
      ≤ ∑ p ∈ S, ∏ i, (1 + (b i - (8 : ℝ)⁻¹ * p i) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun p _ => remWt_le_prod _
    _ ≤ ∑ p ∈ Fintype.piFinset (fun i => S.image (fun q => q i)),
          ∏ i, (1 + (b i - (8 : ℝ)⁻¹ * p i) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image.2 ⟨p, hp, rfl⟩
    _ = ∏ i, ∑ n ∈ S.image (fun q => q i), (1 + (b i - (8 : ℝ)⁻¹ * n) ^ 2)⁻¹ :=
        (Finset.prod_univ_sum (fun i => S.image (fun q => q i))
          (fun i n => (1 + (b i - (8 : ℝ)⁻¹ * n) ^ 2)⁻¹)).symm
    _ ≤ ∏ _i : Fin 3, H :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun n _ => by positivity)
          fun i _ => hH _ _
    _ = H ^ 3 := by simp

theorem exists_sum_remCellWt_le :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ (x : ParabolicSpace) (S : Finset LatticeIndex),
      ∑ j ∈ S, remCellWt x j ≤ W := by
  classical
  obtain ⟨H, hH0, hH⟩ := exists_sum_remWt_le
  refine ⟨65 * H, by positivity, fun x S => ?_⟩
  have e : ∀ (a : ℤ) (p : Fin 3 → ℤ), remWt (x.2 - (latticePoint 3 (a, p)).2) =
      remWt (fun i => x.2 i - (8 : ℝ)⁻¹ * p i) := fun a p => by
    congr 1
    funext i
    simp only [Pi.sub_apply, latticePoint_snd]
    norm_num
  calc ∑ j ∈ S, remCellWt x j
      = ∑ j ∈ S.filter (fun j => j.1 ∈ Finset.Icc (-1 : ℤ) 63),
          remWt (x.2 - (latticePoint 3 j).2) := by
        rw [Finset.sum_filter]; rfl
    _ ≤ ∑ j ∈ (Finset.Icc (-1 : ℤ) 63) ×ˢ (S.image Prod.snd),
          remWt (x.2 - (latticePoint 3 j).2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => remWt_nonneg _
        obtain ⟨hjS, hj1⟩ := Finset.mem_filter.1 hj
        exact Finset.mem_product.2 ⟨hj1, Finset.mem_image.2 ⟨j, hjS, rfl⟩⟩
    _ = ∑ a ∈ Finset.Icc (-1 : ℤ) 63, ∑ p ∈ S.image Prod.snd,
          remWt (fun i => x.2 i - (8 : ℝ)⁻¹ * p i) := by
        rw [Finset.sum_product]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => e a p
    _ ≤ ∑ _a ∈ Finset.Icc (-1 : ℤ) 63, H :=
        Finset.sum_le_sum fun a _ => hH x.2 _
    _ = 65 * H := by
        rw [Finset.sum_const, Int.card_Icc]
        norm_num

theorem summable_remCellWt (x : ParabolicSpace) : Summable (remCellWt x) := by
  obtain ⟨W, -, hW⟩ := exists_sum_remCellWt_le
  exact summable_of_sum_le (fun j => remCellWt_nonneg x j) (hW x)

theorem tsum_remCellWt_le :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ x : ParabolicSpace, ∑' j, remCellWt x j ≤ W := by
  obtain ⟨W, hW0, hW⟩ := exists_sum_remCellWt_le
  exact ⟨W, hW0, fun x => (summable_remCellWt x).tsum_le_of_sum_le (hW x)⟩

end RegularityStructures

end
