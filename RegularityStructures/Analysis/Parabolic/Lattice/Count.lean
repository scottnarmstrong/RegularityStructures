/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Lattice.Cell
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Round

/-!
# Counting lattice points in parabolic boxes

`latticeBox n x rt rs` is a finite box of lattice indices containing every `k` whose lattice point
`latticePoint n k` lies within time distance `rt` and space distance `rs` of `x`; its cardinality is
at most `(2·4^n·rt + 2)(2·2^n·rs + 2)³` (`card_latticeBox_le`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- A box of lattice indices around `x`: time indices in `[4^n (x₀ - rt), 4^n (x₀ + rt)]` and
space indices in `[2^n (xᵢ - rs), 2^n (xᵢ + rs)]`. -/
def latticeBox (n : ℕ) (x : ParabolicSpace) (rt rs : ℝ) : Finset LatticeIndex :=
  Finset.Icc ⌈(4 : ℝ) ^ n * (x.1 - rt)⌉ ⌊(4 : ℝ) ^ n * (x.1 + rt)⌋ ×ˢ
    Fintype.piFinset fun i =>
      Finset.Icc ⌈(2 : ℝ) ^ n * (x.2 i - rs)⌉ ⌊(2 : ℝ) ^ n * (x.2 i + rs)⌋

end RegularityStructures

end

public section

namespace RegularityStructures

private theorem four_pow_eq (n : ℕ) : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

private theorem card_Icc_ceil_floor_le {x y : ℝ} (h : x ≤ y) :
    ((Finset.Icc ⌈x⌉ ⌊y⌋).card : ℝ) ≤ y - x + 1 := by
  rw [Int.card_Icc]
  by_cases h0 : 0 ≤ ⌊y⌋ + 1 - ⌈x⌉
  · have : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℤ) : ℝ) = ((⌊y⌋ + 1 - ⌈x⌉ : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg h0]
    have h2 : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℝ) = ((⌊y⌋ + 1 - ⌈x⌉ : ℤ) : ℝ) := by
      exact_mod_cast this
    rw [h2]
    push_cast
    linarith [Int.floor_le y, Int.le_ceil x]
  · rw [Int.toNat_of_nonpos (not_le.1 h0).le]
    simp
    linarith

theorem mem_latticeBox {n : ℕ} {x : ParabolicSpace} {rt rs : ℝ} {k : LatticeIndex}
    (h0 : |(latticePoint n k).1 - x.1| ≤ rt)
    (hi : ∀ i, |(latticePoint n k).2 i - x.2 i| ≤ rs) : k ∈ latticeBox n x rt rs := by
  have hD : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hk1 : (k.1 : ℝ) = (4 : ℝ) ^ n * (latticePoint n k).1 := by
    rw [latticePoint_fst, four_pow_eq]; field_simp
  have hk2 : ∀ i, (k.2 i : ℝ) = (2 : ℝ) ^ n * (latticePoint n k).2 i := fun i => by
    rw [latticePoint_snd]; field_simp
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  simp only [latticeBox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩, fun i => ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩⟩
  · rw [hk1]
    exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 h0).1]) h4.le
  · rw [hk1]
    exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 h0).2]) h4.le
  · rw [hk2 i]
    exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hi i)).1]) hD.le
  · rw [hk2 i]
    exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hi i)).2]) hD.le

theorem card_latticeBox_le {n : ℕ} {x : ParabolicSpace} {rt rs : ℝ} (hrt : 0 ≤ rt) (hrs : 0 ≤ rs) :
    ((latticeBox n x rt rs).card : ℝ) ≤ (2 * 4 ^ n * rt + 2) * (2 * 2 ^ n * rs + 2) ^ 3 := by
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hA : ((Finset.Icc ⌈(4 : ℝ) ^ n * (x.1 - rt)⌉ ⌊(4 : ℝ) ^ n * (x.1 + rt)⌋).card : ℝ) ≤
      2 * 4 ^ n * rt + 2 := by
    have := card_Icc_ceil_floor_le (x := (4 : ℝ) ^ n * (x.1 - rt))
      (y := (4 : ℝ) ^ n * (x.1 + rt)) (by nlinarith)
    nlinarith
  have hB : ∀ i : Fin 3,
      ((Finset.Icc ⌈(2 : ℝ) ^ n * (x.2 i - rs)⌉ ⌊(2 : ℝ) ^ n * (x.2 i + rs)⌋).card : ℝ) ≤
      2 * 2 ^ n * rs + 2 := fun i => by
    have := card_Icc_ceil_floor_le (x := (2 : ℝ) ^ n * (x.2 i - rs))
      (y := (2 : ℝ) ^ n * (x.2 i + rs)) (by nlinarith)
    nlinarith
  unfold latticeBox
  rw [Finset.card_product, Fintype.card_piFinset]
  push_cast
  refine mul_le_mul hA ?_ (by positivity) (by positivity)
  calc (∏ i : Fin 3, ((Finset.Icc ⌈(2 : ℝ) ^ n * (x.2 i - rs)⌉ ⌊(2 : ℝ) ^ n * (x.2 i + rs)⌋).card : ℝ))
      ≤ ∏ _i : Fin 3, (2 * 2 ^ n * rs + 2) :=
        Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => hB i
    _ = (2 * 2 ^ n * rs + 2) ^ 3 := by simp

theorem mem_latticeBox_of_parabolicNorm_le {n : ℕ} {x : ParabolicSpace} {r : ℝ} {k : LatticeIndex}
    (h : parabolicNorm (latticePoint n k - x) ≤ r) : k ∈ latticeBox n x (r ^ 2) r := by
  have hsum : 0 ≤ ∑ i, |(latticePoint n k - x).2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsq : 0 ≤ Real.sqrt |(latticePoint n k - x).1| := Real.sqrt_nonneg _
  unfold parabolicNorm at h
  refine mem_latticeBox ?_ fun i => ?_
  · have h1 : Real.sqrt |(latticePoint n k - x).1| ≤ r := by linarith
    have := (Real.sqrt_le_iff.1 h1).2
    simpa using this
  · have h1 : |(latticePoint n k - x).2 i| ≤ ∑ j, |(latticePoint n k - x).2 j| :=
      Finset.single_le_sum (f := fun j => |(latticePoint n k - x).2 j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have := h1.trans (by linarith : ∑ j, |(latticePoint n k - x).2 j| ≤ r)
    simpa using this

end RegularityStructures

end
