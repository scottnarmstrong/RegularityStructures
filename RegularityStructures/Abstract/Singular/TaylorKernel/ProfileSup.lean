/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TaylorKernel.RemSup
public import RegularityStructures.Analysis.Heat.Schauder.TaylorEstimate
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime

/-!
# Pointwise bound for the parabolic Taylor remainder profile

For `taylorProfile φ σ z u = φ(u + z) - ∑_{|k|_𝔰 < σ} z^k/k! D^k φ(u)` we show

  `|taylorProfile φ σ z u| ≤ ∑_{ℓ ∈ E} d^{|ℓ|_𝔰} B ℓ`

whenever `|z_i| ≤ d^{w_i}` and `|D^ℓ φ| ≤ B ℓ` for all coordinate words `ℓ`, where the finite
list `E` of words (depending only on `σ`) satisfies `σ ≤ |ℓ|_𝔰` for each `ℓ ∈ E`
(`exists_abs_taylorProfile_le_sup`).

Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.18.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem exists_abs_taylorProfile_le_sup (σ : ℝ) :
    ∃ E : List (List (Fin 4)), (∀ ℓ ∈ E, σ ≤ (indexWeight ℓ : ℝ)) ∧
      ∀ {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → ∀ B : List (Fin 4) → ℝ,
        (∀ ℓ u, |lineIter (ℓ.map coordDir) φ u| ≤ B ℓ) → ∀ (z u : ParabolicSpace) (d : ℝ),
        0 ≤ d → (∀ i, |parabolicCoords z i| ≤ d ^ parabolicWeight i) →
        |taylorProfile φ σ z u| ≤ (E.map fun ℓ => d ^ indexWeight ℓ * B ℓ).sum := by
  classical
  obtain ⟨E, hEp, hE⟩ := exists_abs_remJ_le_sup (fun _ : Fin 4 => ⌈σ⌉₊) (List.finRange 4)
  set Out : List (List (Fin 4)) := (taylorOut σ).toList.map fun k => (Finsupp.toMultiset k).toList
    with hOut
  refine ⟨E ++ Out, ?_, ?_⟩
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hE' | hO
    · obtain ⟨j, -, hj⟩ := hEp ℓ hE'
      have h1 := count_le_indexWeight j ℓ
      have h2 : σ ≤ ⌈σ⌉₊ := Nat.le_ceil σ
      have h3 : (⌈σ⌉₊ : ℝ) + 1 ≤ (indexWeight ℓ : ℝ) := by exact_mod_cast hj.trans h1
      linarith
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hO
      have hk' := Finset.mem_toList.1 hk
      have : ¬ (multiDeg k : ℝ) < σ := by
        unfold taylorOut at hk'
        exact (Finset.mem_filter.1 hk').2
      rw [indexWeight_toList]
      exact not_lt.1 this
  · intro φ hφ B hB z u d hd hz
    have hφ' : ContDiff ℝ ∞ fun w => φ (-w) := hφ.comp contDiff_neg
    have hconv : ∀ F : List (Fin 4) → ℝ,
        ∑ k ∈ taylorOut σ, F ((Finsupp.toMultiset k).toList) = (Out.map F).sum := by
      intro F
      rw [hOut, List.map_map]
      exact (Finset.sum_map_toList (taylorOut σ)
        (fun k => F ((Finsupp.toMultiset k).toList))).symm
    rw [taylorProfile_eq hφ, List.map_append, List.sum_append]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine hE (fun i => -parabolicCoords z i) d hd (fun i => by rw [abs_neg]; exact hz i) hφ' B
        (fun ℓ v => ?_) _
      rw [lineIter_reflect hφ, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hB ℓ _
    · rw [← hconv]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, indexWeight_toList]
      have hc := abs_coeffT_le hz k
      have := hB (Finsupp.toMultiset k).toList u
      rw [← multiDirs_eq_map] at this
      exact mul_le_mul hc this (abs_nonneg _) (pow_nonneg hd _)

end RegularityStructures

end
