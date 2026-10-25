/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Lattice.Bump
public import RegularityStructures.Analysis.Heat.Kernel
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Lattice sums for the spatial tails

Elementary lattice estimates used to sum the pieces of the spatial partition of unity of a smooth
kernel with decay `(1 + |x|²)^{-3}`:

* `bump3 a = ∏ latticeBump (a i)` and `hasSum_bump3`: `∑_{k ∈ ℤ³} bump3 (a - k) = 1`;
* `tsum_lat1_le`: `∑_{m ∈ ℤ} (1 + (a - (m+1)/8)²)⁻¹ ≤ latS` uniformly in `a`;
* `summable_remWt_lattice`: `∑_{k ∈ ℤ³} (1 + |a - (k+1)/8|²)^{-3} ≤ latS³` uniformly in `a ∈ ℝ³`.
-/

public section

open Set Finset

namespace RegularityStructures.Potential

/-- The tensor product of the lattice bump on `ℝ³`. -/
@[expose] noncomputable def bump3 (a : Fin 3 → ℝ) : ℝ := ∏ i, latticeBump (a i)

theorem bump3_ne_zero {a : Fin 3 → ℝ} (h : bump3 a ≠ 0) : ∀ i, 0 < a i ∧ a i < 2 := fun i =>
  latticeBump_ne_zero (Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i))

private theorem mem_Icc_floor {s : ℝ} {k : ℤ} (h : latticeBump (s - k) ≠ 0) :
    k ∈ Finset.Icc (⌊s⌋ - 1) ⌊s⌋ := by
  obtain ⟨h1, h2⟩ := latticeBump_ne_zero h
  rw [Finset.mem_Icc]
  constructor
  · have : (⌊s⌋ : ℝ) - 2 < k := by have := Int.floor_le s; linarith
    have : ⌊s⌋ - 2 < k := by exact_mod_cast this
    omega
  · exact Int.le_floor.2 (by linarith)

theorem hasSum_bump3 (a : Fin 3 → ℝ) :
    HasSum (fun k : Fin 3 → ℤ => bump3 (a - fun i => (k i : ℝ))) 1 := by
  set s : Finset (Fin 3 → ℤ) := Fintype.piFinset fun i => Finset.Icc (⌊a i⌋ - 1) ⌊a i⌋ with hs
  have hsum : ∑ k ∈ s, bump3 (a - fun i => (k i : ℝ)) = 1 := by
    unfold bump3
    simp only [Pi.sub_apply]
    rw [hs, ← Finset.prod_univ_sum (fun i => Finset.Icc (⌊a i⌋ - 1) ⌊a i⌋)
      (fun i k => latticeBump (a i - k))]
    refine Finset.prod_eq_one fun i _ => ?_
    exact sum_latticeBump_Icc (by push_cast; linarith [Int.floor_le (a i)])
      (by linarith [Int.lt_floor_add_one (a i)])
  have : HasSum (fun k : Fin 3 → ℤ => bump3 (a - fun i => (k i : ℝ)))
      (∑ k ∈ s, bump3 (a - fun i => (k i : ℝ))) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      by_contra hne
      apply hk
      rw [hs, Fintype.mem_piFinset]
      intro i
      exact mem_Icc_floor (Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ i))
  rwa [hsum] at this

/-- The one-dimensional lattice weight `(1 + (a - (m+1)/8)²)⁻¹`. -/
@[expose] noncomputable def lat1 (a : ℝ) (m : ℤ) : ℝ := (1 + (a - ((m : ℝ) + 1) / 8) ^ 2)⁻¹

/-- The dominating profile `(1 + (max (|j| - 1) 0 / 8)²)⁻¹`. -/
@[expose] noncomputable def latH (j : ℤ) : ℝ := (1 + (max (|(j : ℝ)| - 1) 0 / 8) ^ 2)⁻¹

theorem lat1_nonneg (a : ℝ) (m : ℤ) : 0 ≤ lat1 a m := by unfold lat1; positivity

theorem latH_nonneg (j : ℤ) : 0 ≤ latH j := by unfold latH; positivity

theorem lat1_le_latH (a : ℝ) (m : ℤ) : lat1 a m ≤ latH (m - (⌊8 * a⌋ - 1)) := by
  unfold lat1 latH
  set t : ℝ := a - ((m : ℝ) + 1) / 8 with ht
  have h1 : |(((m - (⌊8 * a⌋ - 1) : ℤ) : ℝ))| - 1 ≤ |8 * t| := by
    have hf0 := Int.floor_le (8 * a)
    have hf1 := Int.lt_floor_add_one (8 * a)
    have e : 8 * t = (8 * a - ⌊8 * a⌋) + (((⌊8 * a⌋ - 1 - m : ℤ) : ℝ)) := by
      rw [ht]; push_cast; ring
    have hj : |(((m - (⌊8 * a⌋ - 1) : ℤ) : ℝ))| = |(((⌊8 * a⌋ - 1 - m : ℤ) : ℝ))| := by
      rw [← abs_neg]; congr 1; push_cast; ring
    rw [hj, e]
    have hfr : 0 ≤ 8 * a - ⌊8 * a⌋ := by linarith
    have hfr1 : 8 * a - ⌊8 * a⌋ ≤ 1 := by linarith
    have := abs_sub_abs_le_abs_sub (((⌊8 * a⌋ - 1 - m : ℤ) : ℝ)) (-(8 * a - ⌊8 * a⌋))
    rw [abs_neg, abs_of_nonneg hfr] at this
    have h2 : |(((⌊8 * a⌋ - 1 - m : ℤ) : ℝ))| - (8 * a - ⌊8 * a⌋) ≤
        |(8 * a - ⌊8 * a⌋) + (((⌊8 * a⌋ - 1 - m : ℤ) : ℝ))| := by
      have := abs_sub_abs_le_abs_sub (((⌊8 * a⌋ - 1 - m : ℤ) : ℝ)) (-(8 * a - ⌊8 * a⌋))
      rw [abs_neg, abs_of_nonneg hfr, sub_neg_eq_add, add_comm] at this
      exact this
    linarith
  have h2 : max (|(((m - (⌊8 * a⌋ - 1) : ℤ) : ℝ))| - 1) 0 / 8 ≤ |t| := by
    have : max (|(((m - (⌊8 * a⌋ - 1) : ℤ) : ℝ))| - 1) 0 ≤ |8 * t| :=
      max_le h1 (abs_nonneg _)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at this
    linarith
  have h3 : (max (|(((m - (⌊8 * a⌋ - 1) : ℤ) : ℝ))| - 1) 0 / 8) ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (by positivity) h2 2
  exact inv_anti₀ (by positivity) (by linarith)

theorem summable_latH : Summable latH := by
  have hs : Summable fun j : ℤ => 256 * (1 / (j : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow.2 (by norm_num)).mul_left 256
  refine Summable.of_norm_bounded_eventually hs ?_
  have hfin : {j : ℤ | |j| < 2}.Finite := by
    refine (Finset.Icc (-1 : ℤ) 1).finite_toSet.subset fun j hj => ?_
    have h2 : |j| < 2 := hj
    have := abs_lt.1 h2
    simp only [Finset.coe_Icc, Set.mem_Icc]
    omega
  filter_upwards [hfin.compl_mem_cofinite] with j hj
  have hj' : 2 ≤ |j| := not_lt.1 hj
  have hj2 : (2 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast hj'
  have hm : max (|(j : ℝ)| - 1) 0 = |(j : ℝ)| - 1 := max_eq_left (by linarith)
  rw [Real.norm_of_nonneg (latH_nonneg j)]
  unfold latH
  rw [hm]
  have hj0 : (0 : ℝ) < (j : ℝ) ^ 2 := by
    have : (0 : ℝ) < |(j : ℝ)| := by linarith
    have h3 : (j : ℝ) ≠ 0 := abs_pos.1 this
    positivity
  have h4 : (j : ℝ) ^ 2 / 256 ≤ ((|(j : ℝ)| - 1) / 8) ^ 2 := by
    rw [div_pow, ← sq_abs (j : ℝ)]
    have : |(j : ℝ)| / 2 ≤ |(j : ℝ)| - 1 := by linarith
    have h5 : (|(j : ℝ)| / 2) ^ 2 ≤ (|(j : ℝ)| - 1) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
    nlinarith [sq_abs (j : ℝ)]
  have h6 : 256 * (1 / (j : ℝ) ^ 2) * ((j : ℝ) ^ 2 / 256) = 1 := by
    have : (j : ℝ) ≠ 0 := abs_pos.1 (by linarith)
    field_simp
  rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
  calc (1 : ℝ) = 256 * (1 / (j : ℝ) ^ 2) * ((j : ℝ) ^ 2 / 256) := h6.symm
    _ ≤ 256 * (1 / (j : ℝ) ^ 2) * (1 + ((|(j : ℝ)| - 1) / 8) ^ 2) := by
        gcongr; linarith

/-- The uniform constant of the one-dimensional lattice sums. -/
@[expose] noncomputable def latS : ℝ := ∑' j, latH j

theorem latS_nonneg : 0 ≤ latS := tsum_nonneg latH_nonneg

theorem sum_lat1_le (a : ℝ) (s : Finset ℤ) : ∑ m ∈ s, lat1 a m ≤ latS := by
  set m₀ : ℤ := ⌊8 * a⌋ - 1
  calc ∑ m ∈ s, lat1 a m ≤ ∑ m ∈ s, latH (m - m₀) :=
        Finset.sum_le_sum fun m _ => lat1_le_latH a m
    _ = ∑ j ∈ s.image (fun m => m - m₀), latH j := by
        rw [Finset.sum_image]
        intro x _ y _ h
        simpa using h
    _ ≤ latS := summable_latH.sum_le_tsum _ fun j _ => latH_nonneg j

/-- The three-dimensional lattice weight `∏ᵢ (1 + (aᵢ - (kᵢ+1)/8)²)⁻¹`. -/
@[expose] noncomputable def latRem (a : Fin 3 → ℝ) (k : Fin 3 → ℤ) : ℝ := ∏ i, lat1 (a i) (k i)

theorem latRem_nonneg (a : Fin 3 → ℝ) (k : Fin 3 → ℤ) : 0 ≤ latRem a k :=
  Finset.prod_nonneg fun _ _ => lat1_nonneg _ _

theorem sum_latRem_le (a : Fin 3 → ℝ) (F : Finset (Fin 3 → ℤ)) :
    ∑ k ∈ F, latRem a k ≤ latS ^ 3 := by
  have hsub : F ⊆ Fintype.piFinset fun i => F.image (fun k => k i) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    exact fun i => Finset.mem_image_of_mem _ hk
  calc ∑ k ∈ F, latRem a k ≤ ∑ k ∈ Fintype.piFinset (fun i => F.image (fun k => k i)), latRem a k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => latRem_nonneg a k
    _ = ∏ i, ∑ m ∈ F.image (fun k => k i), lat1 (a i) m := by
        unfold latRem
        rw [Finset.prod_univ_sum (fun i => F.image (fun k => k i)) (fun i m => lat1 (a i) m)]
    _ ≤ ∏ _i : Fin 3, latS :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun m _ => lat1_nonneg _ _)
          fun i _ => sum_lat1_le (a i) _
    _ = latS ^ 3 := by simp

theorem summable_latRem (a : Fin 3 → ℝ) : Summable (latRem a) :=
  summable_of_sum_le (fun k => latRem_nonneg a k) (fun F => sum_latRem_le a F)

theorem tsum_latRem_le (a : Fin 3 → ℝ) : ∑' k, latRem a k ≤ latS ^ 3 :=
  (summable_latRem a).tsum_le_of_sum_le fun F => sum_latRem_le a F

/-- The decay weight `(1 + |y|²)⁻³` is dominated by the product of one-dimensional weights. -/
theorem inv_one_add_sqNorm3_pow_le (y : Fin 3 → ℝ) :
    (1 + sqNorm3 y)⁻¹ ^ 3 ≤ ∏ i, (1 + y i ^ 2)⁻¹ := by
  have hle : ∀ i, 1 + y i ^ 2 ≤ 1 + sqNorm3 y := fun i => by
    unfold sqNorm3
    have := Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
    linarith
  have h1 : ∏ i, (1 + y i ^ 2) ≤ (1 + sqNorm3 y) ^ 3 := by
    calc ∏ i, (1 + y i ^ 2) ≤ ∏ _i : Fin 3, (1 + sqNorm3 y) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => hle i
      _ = _ := by simp
  have h0 : 0 < ∏ i, (1 + y i ^ 2) := Finset.prod_pos fun i _ => by positivity
  rw [inv_pow, Finset.prod_inv_distrib]
  exact inv_anti₀ h0 h1

end RegularityStructures.Potential

end
