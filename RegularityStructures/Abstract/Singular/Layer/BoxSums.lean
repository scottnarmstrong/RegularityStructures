/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.Weighted
public import RegularityStructures.Abstract.Singular.Layer.Counting
public import RegularityStructures.Abstract.Singular.LatticeApprox
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Sums over lattice boxes in the layer bound

* the support box of `ψ χ_{m,k}`;
* sums of indicator-type terms over a box;
* the regular part: `∑_{k ∈ box} 1_{z_0 > 0} c₁ G(k_0) ≤ 125 Λ³ · c₁ κ Λ² λ^{-θ}`;
* the algebra turning `λ^{-5} r^{5+a} Λ^j` into `r^a λ^{-θ}`-type expressions.
-/

public section

open Finset

namespace RegularityStructures.Layer

theorem mem_latticeBox_of_support {ψ : ParabolicSpace → ℝ} {x : ParabolicSpace} {R : ℝ}
    (hψ : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) (m : ℕ) (k : LatticeIndex)
    (w : ParabolicSpace) (h : ψ w * latticeCell m k w ≠ 0) :
    k ∈ latticeBox m x ((R + 8 * ((2 : ℝ) ^ m)⁻¹) ^ 2) (R + 8 * ((2 : ℝ) ^ m)⁻¹) := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have hw : parabolicNorm (w - x) ≤ R := by
    by_contra hc; exact h1 (hψ w (not_le.1 hc))
  have hk := parabolicNorm_sub_latticePoint_le h2
  refine mem_latticeBox_of_parabolicNorm_le ?_
  have e : latticePoint m k - x = (w - x) + (latticePoint m k - w) := by abel
  rw [e]
  refine (parabolicNorm_add_le _ _).trans ?_
  rw [parabolicNorm_sub_comm (latticePoint m k)]
  linarith

theorem sum_ite_mem_le {α : Type*} [DecidableEq α] (s T : Finset α) {X : ℝ} (hX : 0 ≤ X) :
    ∑ l ∈ s, (if l ∈ T then X else 0) ≤ (T.card : ℝ) * X := by
  rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
    hX

/-- Double sum of the per-pair bounds. -/
theorem sum_sum_ite_le {s' s : Finset LatticeIndex} (Lb : LatticeIndex → Finset LatticeIndex)
    (X : LatticeIndex → ℝ) (hX : ∀ k, 0 ≤ X k) {Lc : ℝ} (hL : ∀ k, ((Lb k).card : ℝ) ≤ Lc) :
    ∑ k ∈ s', ∑ l ∈ s, (if l ∈ Lb k then X k else 0) ≤ Lc * ∑ k ∈ s', X k := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  exact (sum_ite_mem_le s (Lb k) (hX k)).trans
    (mul_le_mul_of_nonneg_right (hL k) (hX k))

theorem latticePoint_fst_pos_iff (m : ℕ) (k : LatticeIndex) :
    0 < (latticePoint m k).1 ↔ 0 < k.1 := by
  rw [latticePoint_fst]
  have : (0 : ℝ) < (((2 : ℝ) ^ m)⁻¹) ^ 2 := by positivity
  rw [mul_pos_iff_of_pos_left this]
  exact_mod_cast Iff.rfl

/-- The regular part summed over the box `s'`. -/
theorem sum_regular_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ < 2) {n : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hΛ : 32 ≤ lam * 2 ^ n) (x : ParabolicSpace) {c : ℝ} (hc : 0 ≤ c) :
    ∑ k ∈ latticeBox (n + 1) x ((lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)
        (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹),
      (if 0 < (latticePoint (n + 1) k).1 then c * weightBound θ (n + 1) k.1 else 0) ≤
    125 * (lam * 2 ^ n) ^ 3 * (c * (11 * (2 : ℝ) ^ θ * (1 + (2 : ℝ) ^ θ / (1 - θ / 2)) *
      (lam * 2 ^ n) ^ 2 * lam ^ (-θ))) := by
  have e : ∀ k : LatticeIndex, (if 0 < (latticePoint (n + 1) k).1 then c * weightBound θ (n + 1) k.1
      else 0) = (fun j : ℤ => if 0 < j then c * weightBound θ (n + 1) j else 0) k.1 := by
    intro k
    simp only [latticePoint_fst_pos_iff]
  rw [Finset.sum_congr rfl fun k _ => e k, sum_latticeBox_fst (n + 1) x _ _
    (fun j : ℤ => if 0 < j then c * weightBound θ (n + 1) j else 0)]
  refine mul_le_mul (card_latticeBox_space_succ_le hlam hΛ x) ?_ (Finset.sum_nonneg fun j _ => ?_)
    (by positivity)
  · have h := sum_weightBound_le hθ0 hθ2 hlam hlam1
      (Finset.Icc ⌈(4 : ℝ) ^ (n + 1) * (x.1 - (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)⌉
        ⌊(4 : ℝ) ^ (n + 1) * (x.1 + (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)⌋)
      (card_latticeBox_time_succ_le hlam hΛ x)
    have : ∑ j ∈ Finset.Icc ⌈(4 : ℝ) ^ (n + 1) * (x.1 - (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)⌉
        ⌊(4 : ℝ) ^ (n + 1) * (x.1 + (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)⌋,
        (if 0 < j then c * weightBound θ (n + 1) j else 0) =
        c * ∑ j ∈ Finset.Icc ⌈(4 : ℝ) ^ (n + 1) * (x.1 - (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)⌉
        ⌊(4 : ℝ) ^ (n + 1) * (x.1 + (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)⌋,
          (if 0 < j then weightBound θ (n + 1) j else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h hc
  · split_ifs
    · exact mul_nonneg hc (weightBound_nonneg _ _ _)
    · exact le_rfl

theorem alg_regular {n : ℕ} {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    (lam ^ 5)⁻¹ * (((2 : ℝ) ^ n)⁻¹) ^ (5 + a) * (lam * 2 ^ n) ^ 5 = (((2 : ℝ) ^ n)⁻¹) ^ a := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hr : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  rw [Real.rpow_add hr, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow]
  field_simp

theorem alg_near {n : ℕ} {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    (lam ^ 5)⁻¹ * (((2 : ℝ) ^ n)⁻¹) ^ (5 + a) * (lam * 2 ^ n) ^ 3 =
      lam ^ (-2 : ℝ) * (((2 : ℝ) ^ n)⁻¹) ^ (2 + a) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hr : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have e1 : (5 : ℝ) + a = 3 + (2 + a) := by ring
  rw [e1, Real.rpow_add hr, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow,
    Real.rpow_neg hlam.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

end RegularityStructures.Layer

end
