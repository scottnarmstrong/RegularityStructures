/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Lattice.Cell
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Partition of unity from the lattice cells

For every `n` and `w`, the cells `latticeCell n k w` sum to one, and only the cells in a
finite box around `S^{2^n} w` are nonzero.
-/

public section

namespace RegularityStructures

/-- The finite box of indices that can contribute at the dilated point `u`. -/
private noncomputable def cellBox (u : ParabolicSpace) : Finset LatticeIndex :=
  (Finset.Icc (⌊u.1⌋ - 1) ⌊u.1⌋) ×ˢ
    Fintype.piFinset fun i => Finset.Icc (⌊u.2 i⌋ - 1) ⌊u.2 i⌋

private theorem mem_Icc_floor_of_latticeBump_ne_zero {s : ℝ} {k : ℤ}
    (h : latticeBump (s - k) ≠ 0) : k ∈ Finset.Icc (⌊s⌋ - 1) ⌊s⌋ := by
  obtain ⟨h1, h2⟩ := latticeBump_ne_zero h
  rw [Finset.mem_Icc]
  constructor
  · have : (⌊s⌋ : ℝ) - 2 < k := by have := Int.floor_le s; linarith
    have : ⌊s⌋ - 2 < k := by exact_mod_cast this
    omega
  · exact Int.le_floor.2 (by linarith)

private theorem support_latticeCell_subset (n : ℕ) (w : ParabolicSpace) :
    ∀ k, latticeCell n k w ≠ 0 → k ∈ cellBox (parabolicDilate ((2 : ℝ) ^ n) w) := by
  intro k hk
  have hne := hk
  unfold latticeCell latticeBump4 at hne
  rw [mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hne
  simp only [cellBox, Finset.mem_product, Fintype.mem_piFinset]
  exact ⟨mem_Icc_floor_of_latticeBump_ne_zero hne.1, fun i =>
    mem_Icc_floor_of_latticeBump_ne_zero (hne.2 i (Finset.mem_univ i))⟩

private theorem sum_cellBox (n : ℕ) (w : ParabolicSpace) :
    ∑ k ∈ cellBox (parabolicDilate ((2 : ℝ) ^ n) w), latticeCell n k w = 1 := by
  set u := parabolicDilate ((2 : ℝ) ^ n) w
  unfold cellBox
  have hcell : ∀ k : LatticeIndex, latticeCell n k w =
      latticeBump (u.1 - k.1) * ∏ i, latticeBump (u.2 i - k.2 i) := fun k => by
    simp [latticeCell, latticeBump4, u, latticeCoe]
  simp_rw [hcell]
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.prod_univ_sum (fun i => Finset.Icc (⌊u.2 i⌋ - 1) ⌊u.2 i⌋)
    (fun i k => latticeBump (u.2 i - k))]
  have key : ∀ s : ℝ, ∑ j ∈ Finset.Icc (⌊s⌋ - 1) ⌊s⌋, latticeBump (s - j) = 1 := fun s =>
    sum_latticeBump_Icc (by push_cast; linarith [Int.floor_le s])
      (by linarith [Int.lt_floor_add_one s])
  simp_rw [key, Finset.prod_const_one, mul_one]
  exact key _


theorem finite_support_latticeCell (n : ℕ) (w : ParabolicSpace) :
    (Function.support fun k => latticeCell n k w).Finite :=
  (cellBox (parabolicDilate ((2 : ℝ) ^ n) w)).finite_toSet.subset fun k hk =>
    support_latticeCell_subset n w k hk

theorem finsum_latticeCell (n : ℕ) (w : ParabolicSpace) :
    ∑ᶠ k, latticeCell n k w = 1 := by
  rw [finsum_eq_sum_of_support_subset _
    (s := cellBox (parabolicDilate ((2 : ℝ) ^ n) w)) fun k hk => support_latticeCell_subset n w k hk]
  exact sum_cellBox n w

theorem sum_latticeCell_eq_one {n : ℕ} {w : ParabolicSpace} {s : Finset LatticeIndex}
    (hs : ∀ k, latticeCell n k w ≠ 0 → k ∈ s) : ∑ k ∈ s, latticeCell n k w = 1 := by
  rw [← finsum_latticeCell n w]
  exact (finsum_eq_sum_of_support_subset _ fun k hk => hs k hk).symm

end RegularityStructures

end
