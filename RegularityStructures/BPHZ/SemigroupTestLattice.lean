/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Uniform lattice sums of a quadratic decay profile

For `a ∈ ℝ³` the lattice sum `∑_{k ∈ ℤ³} ∏ᵢ (1 + |aᵢ + kᵢ|)⁻²` converges and is bounded uniformly
in `a` (`exists_lattice_sum_le`).  The proof shifts `k` by `⌊a⌋` to reduce to
`aᵢ ∈ [0, 1)`, where `(1 + |aᵢ + kᵢ|)⁻² ≤ 4 (1 + |kᵢ|)⁻²`, and sums the product over `ℤ³` as the
cube of the one-dimensional sum (`summable_prod_pi_int`).
-/

public section

open scoped BigOperators

namespace RegularityStructures

theorem summable_int_inv_one_add_abs_sq :
    Summable (fun m : ℤ => ((1 + |(m : ℝ)|) ^ 2)⁻¹) := by
  have h1 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    have := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 (one_lt_two : 1 < 2))
    simpa [one_div] using this
  have hpos : Summable (fun n : ℕ => ((1 + |((n : ℤ) : ℝ)|) ^ 2)⁻¹) := by
    refine h1.congr fun n => ?_
    simp [abs_of_nonneg, add_comm]
  have hneg : Summable (fun n : ℕ => ((1 + |((-(n : ℤ) : ℤ) : ℝ)|) ^ 2)⁻¹) := by
    refine h1.congr fun n => ?_
    simp [add_comm]
  exact Summable.of_nat_of_neg hpos hneg

/-- Sum over `ℤⁿ` of a product of one-dimensional summands. -/
theorem summable_prod_pi_int {f : ℤ → ℝ} (hf0 : ∀ m, 0 ≤ f m) (hf : Summable f) :
    ∀ n : ℕ, Summable (fun k : Fin n → ℤ => ∏ i, f (k i)) ∧
      ∑' k : Fin n → ℤ, ∏ i, f (k i) = (∑' m, f m) ^ n := by
  intro n
  induction n with
  | zero => exact ⟨Summable.of_finite, by simp⟩
  | succ n ih =>
    obtain ⟨ihs, iht⟩ := ih
    have hF0 : ∀ k : Fin n → ℤ, 0 ≤ ∏ i, f (k i) := fun k => Finset.prod_nonneg fun i _ => hf0 _
    have hFs : Summable (fun p : ℤ × (Fin n → ℤ) => f p.1 * ∏ i, f (p.2 i)) :=
      Summable.mul_of_nonneg (f := f) (g := fun k : Fin n → ℤ => ∏ i, f (k i)) hf ihs
        (fun m => hf0 m) (fun k => hF0 k)
    have hcomp : ∀ p : ℤ × (Fin n → ℤ),
        ∏ i, f (((Fin.consEquiv (fun _ => ℤ)) p) i) = f p.1 * ∏ i, f (p.2 i) := by
      intro p
      simp [Fin.prod_univ_succ, Fin.consEquiv]
    have hfn : Summable (fun m => ‖f m‖) := by
      simpa only [Real.norm_of_nonneg (hf0 _)] using hf
    have hgn : Summable (fun k : Fin n → ℤ => ‖∏ i, f (k i)‖) := by
      simpa only [Real.norm_of_nonneg (hF0 _)] using ihs
    refine ⟨?_, ?_⟩
    · refine (Fin.consEquiv (fun _ => ℤ)).summable_iff.1 ?_
      refine hFs.congr fun p => ?_
      exact (hcomp p).symm
    · calc ∑' k : Fin (n + 1) → ℤ, ∏ i, f (k i)
          = ∑' p : ℤ × (Fin n → ℤ), ∏ i, f (((Fin.consEquiv (fun _ => ℤ)) p) i) :=
            ((Fin.consEquiv (fun _ => ℤ)).tsum_eq (fun k : Fin (n + 1) → ℤ => ∏ i, f (k i))).symm
        _ = ∑' p : ℤ × (Fin n → ℤ), f p.1 * ∏ i, f (p.2 i) := tsum_congr hcomp
        _ = (∑' m, f m) * ∑' k : Fin n → ℤ, ∏ i, f (k i) :=
            (tsum_mul_tsum_of_summable_norm (f := f) (g := fun k : Fin n → ℤ => ∏ i, f (k i))
              hfn hgn).symm
        _ = _ := by rw [iht, pow_succ, mul_comm]

/-- Shifted quadratic profile bound: for `β ∈ [0, 1)` and `k ∈ ℤ`,
`(1 + |β + k|)⁻² ≤ 4 (1 + |k|)⁻²`. -/
theorem inv_one_add_abs_sq_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (k : ℤ) :
    ((1 + |β + (k : ℝ)|) ^ 2)⁻¹ ≤ 4 * ((1 + |(k : ℝ)|) ^ 2)⁻¹ := by
  have h : (1 + |(k : ℝ)|) ≤ 2 * (1 + |β + (k : ℝ)|) := by
    rcases le_or_gt 0 (k : ℝ) with hk | hk
    · rw [abs_of_nonneg hk, abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_neg hk]
      have := neg_abs_le (β + (k : ℝ))
      have := abs_nonneg (β + (k : ℝ))
      linarith [neg_le_abs (β + (k : ℝ)), le_abs_self (β + (k : ℝ))]
  have hp : 0 < 1 + |β + (k : ℝ)| := by positivity
  have hq : 0 < 1 + |(k : ℝ)| := by positivity
  have h2 : (1 + |(k : ℝ)|) ^ 2 ≤ (2 * (1 + |β + (k : ℝ)|)) ^ 2 :=
    pow_le_pow_left₀ hq.le h 2
  rw [mul_pow] at h2
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith

/-- **Uniform lattice sum.**  There is `L` with
`∑_{k ∈ ℤ³} ∏ᵢ (1 + |aᵢ + kᵢ|)⁻² ≤ L` for every `a ∈ ℝ³`. -/
theorem exists_lattice_sum_le : ∃ L : ℝ, 0 ≤ L ∧ ∀ a : Fin 3 → ℝ,
    Summable (fun k : Fin 3 → ℤ => ∏ i, ((1 + |a i + (k i : ℝ)|) ^ 2)⁻¹) ∧
      ∑' k : Fin 3 → ℤ, ∏ i, ((1 + |a i + (k i : ℝ)|) ^ 2)⁻¹ ≤ L := by
  set F : ℤ → ℝ := fun m => 4 * ((1 + |(m : ℝ)|) ^ 2)⁻¹ with hF
  have hF0 : ∀ m, 0 ≤ F m := fun m => by positivity
  have hFs : Summable F := summable_int_inv_one_add_abs_sq.mul_left 4
  obtain ⟨hGs, hGt⟩ := summable_prod_pi_int hF0 hFs 3
  refine ⟨(∑' m, F m) ^ 3, pow_nonneg (tsum_nonneg hF0) 3, fun a => ?_⟩
  set n : Fin 3 → ℤ := fun i => -⌊a i⌋ with hn
  set P : (Fin 3 → ℤ) → ℝ := fun k => ∏ i, ((1 + |a i + (k i : ℝ)|) ^ 2)⁻¹ with hP
  have hP0 : ∀ k, 0 ≤ P k := fun k => Finset.prod_nonneg fun i _ => by positivity
  have hle : ∀ k, P (k + n) ≤ ∏ i, F (k i) := by
    intro k
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    have h := inv_one_add_abs_sq_le (Int.fract_nonneg (a i)) (Int.fract_lt_one (a i)) (k i)
    have e : a i + (((k + n) i : ℤ) : ℝ) = Int.fract (a i) + (k i : ℝ) := by
      simp only [Pi.add_apply, hn, Int.cast_add, Int.cast_neg, Int.fract]
      ring
    rw [e]
    exact h
  have hPs : Summable (fun k => P (k + n)) :=
    Summable.of_nonneg_of_le (fun k => hP0 _) hle hGs
  have hPs' : Summable P := (Equiv.addRight n).summable_iff.1 hPs
  refine ⟨hPs', ?_⟩
  calc ∑' k, P k = ∑' k, P (k + n) := ((Equiv.addRight n).tsum_eq P).symm
    _ ≤ ∑' k : Fin 3 → ℤ, ∏ i, F (k i) := hPs.tsum_le_tsum hle hGs
    _ = _ := hGt

end RegularityStructures

end
