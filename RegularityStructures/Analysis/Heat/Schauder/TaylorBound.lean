/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorTy

/-!
# Pointwise bound for the iterated Taylor polynomial

`exists_abs_tyOp_le`: for `|s_j| ≤ d^{w_j}` (`w_j` the parabolic weight of coordinate `j`),
`|tyOp s m J ψ (w)| ≤ ∑_{K ∈ W} d^{|K|_𝔰} |D^K ψ (w)|` for a finite list `W` of derivative words
depending only on `(m, J)`.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem indexWeight_replicate (p : ℕ) (j : Fin 4) :
    indexWeight (List.replicate p j) = p * parabolicWeight j := by
  induction p with
  | zero => simp
  | succ p ih => rw [List.replicate_succ, indexWeight_cons, ih]; ring

theorem sum_list_range_eq (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ p ∈ Finset.range n, f p := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_flatMap_eq {α β : Type*} (l : List α) (f : α → List β) (g : β → ℝ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem exists_abs_tyOp_le (m : Fin 4 → ℕ) : ∀ (J : List (Fin 4)),
    ∃ W : List (List (Fin 4)), ∀ (s : Fin 4 → ℝ) (d : ℝ), 0 ≤ d →
      (∀ j, |s j| ≤ d ^ parabolicWeight j) → ∀ {ψ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ ψ →
      ∀ w, |tyOp s m J ψ w| ≤
        (W.map fun K => d ^ indexWeight K * |lineIter (K.map coordDir) ψ w|).sum
  | [] => ⟨[[]], fun s d _ _ ψ _ w => by simp [tyOp]⟩
  | j :: J => by
    obtain ⟨W', hW'⟩ := exists_abs_tyOp_le m J
    refine ⟨W'.flatMap fun K => (List.range (m j + 1)).map fun p => K ++ List.replicate p j,
      fun s d hd hs ψ hψ w => ?_⟩
    have hψ' := contDiff_tayOp hψ (coordDir j) (s j) (m j)
    refine (hW' s d hd hs hψ' w).trans ?_
    rw [sum_flatMap_eq]
    refine List.sum_le_sum fun K _ => ?_
    rw [List.map_map, sum_list_range_eq]
    simp only [Function.comp]
    have e : lineIter (K.map coordDir) (tayOp (coordDir j) (s j) (m j) ψ) w =
        ∑ p ∈ Finset.range (m j + 1), ((((Nat.factorial p : ℕ) : ℝ)⁻¹ * s j ^ p) *
          lineIter ((K ++ List.replicate p j).map coordDir) ψ w) := by
      rw [lineIter_tayOp hψ, tayOp_eq]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [List.map_append, List.map_replicate, lineIter_append, lineIter_replicate,
        lineIter_iterate_dirDeriv hψ]
    rw [e]
    calc d ^ indexWeight K * |∑ p ∈ Finset.range (m j + 1), ((((Nat.factorial p : ℕ) : ℝ)⁻¹ *
          s j ^ p) * lineIter ((K ++ List.replicate p j).map coordDir) ψ w)|
        ≤ d ^ indexWeight K * ∑ p ∈ Finset.range (m j + 1), |(((Nat.factorial p : ℕ) : ℝ)⁻¹ *
          s j ^ p) * lineIter ((K ++ List.replicate p j).map coordDir) ψ w| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hd _)
      _ = ∑ p ∈ Finset.range (m j + 1), d ^ indexWeight K * |(((Nat.factorial p : ℕ) : ℝ)⁻¹ *
          s j ^ p) * lineIter ((K ++ List.replicate p j).map coordDir) ψ w| := Finset.mul_sum _ _ _
      _ ≤ ∑ p ∈ Finset.range (m j + 1), d ^ indexWeight (K ++ List.replicate p j) *
          |lineIter ((K ++ List.replicate p j).map coordDir) ψ w| := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [indexWeight_append, indexWeight_replicate, pow_add, abs_mul, abs_mul, abs_pow,
          abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
        have hf : ((Nat.factorial p : ℕ) : ℝ)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos p)
        have h1 : |s j| ^ p ≤ d ^ (p * parabolicWeight j) := by
          rw [mul_comm, pow_mul]
          exact pow_le_pow_left₀ (abs_nonneg _) (hs j) p
        have h2 : ((Nat.factorial p : ℕ) : ℝ)⁻¹ * |s j| ^ p ≤ d ^ (p * parabolicWeight j) := by
          calc _ ≤ 1 * |s j| ^ p := mul_le_mul_of_nonneg_right hf (pow_nonneg (abs_nonneg _) _)
            _ ≤ _ := by rw [one_mul]; exact h1
        have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg
          (lineIter ((K ++ List.replicate p j).map coordDir) ψ w))
        have h4 := mul_le_mul_of_nonneg_left h3 (pow_nonneg hd (indexWeight K))
        linarith [h4]

end RegularityStructures

end
