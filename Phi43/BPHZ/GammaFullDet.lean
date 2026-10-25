/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullEntries
import Mathlib.Tactic
public import Phi43.Structure.ModelSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The symbols below `γ = 1 + 3κ` and the deterministic entries

* `eq_random_of_not_mem_gammaFullDeterministic`: a symbol `i` with `deg i < γ` and `(i, j)` outside
  `D_Γ^full = gammaFullDeterministic` is one of the nine random symbols (`IsGammaFullRandom`);
  `X₀`, `XᵢXⱼ` (degree `2`) and `I(Ψ)` (degree `3/2 - κ`) are not below `γ`.
* `abs_structureGroupMap_entry_le_of_mem_gammaFullDeterministic`: for `(i, j) ∈ D_Γ^full` with
  `deg j < deg i` the entry is bounded by `d^(deg i - deg j)` (constant `1`) when all spatial shifts
  are at most `d`.
* `structureGroupMap_entry_eq_of_mem_gammaFullDeterministic`: it depends on the shift only.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The symbols below `γ`: deterministic or one of the nine random symbols.** -/
theorem eq_random_of_not_mem_gammaFullDeterministic (κ : Kappa) {i j : Symbol}
    (hi : homogeneity κ i < gamma κ) (hij : (i, j) ∉ gammaFullDeterministic) :
    IsGammaFullRandom i := by
  have hk0 : 0 < κ.1 := κ.2.1
  have hk1 : κ.1 < 1 / 16 := κ.2.2
  cases i <;> simp only [homogeneity, gamma] at hi <;>
    first
    | (exfalso; linarith)
    | (exfalso; apply hij; simp [gammaFullDeterministic]; done)
    | simp [IsGammaFullRandom]

theorem homogeneity_x_sub_one (κ : Kappa) (k : Fin 3) :
    homogeneity κ (Symbol.x k) - homogeneity κ Symbol.one = 1 := by
  simp only [homogeneity]; ring

theorem homogeneity_psiX_sub_psi (κ : Kappa) (k : Fin 3) :
    homogeneity κ (Symbol.psiX k) - homogeneity κ Symbol.psi = 1 := by
  simp only [homogeneity]; ring

theorem homogeneity_psiSqX_sub_psiSq (κ : Kappa) (k : Fin 3) :
    homogeneity κ (Symbol.psiSqX k) - homogeneity κ Symbol.psiSq = 1 := by
  simp only [homogeneity]; ring

/-- **The deterministic entries are bounded by `d^(deg i - deg j)`.** -/
theorem abs_structureGroupMap_entry_le_of_mem_gammaFullDeterministic (κ : Kappa) (g : G)
    {d : ℝ} (hd : 0 ≤ d) (hg : ∀ k : Fin 3, |g.shift k.succ| ≤ d) {i j : Symbol}
    (hp : (i, j) ∈ gammaFullDeterministic) (hlt : homogeneity κ j < homogeneity κ i) :
    |structureGroupMap g (basis i) j| ≤ 1 * d ^ (homogeneity κ i - homogeneity κ j) := by
  have hne : j ≠ i := fun h => by subst h; exact lt_irrefl _ hlt
  have hpos : 0 ≤ 1 * d ^ (homogeneity κ i - homogeneity κ j) := by
    rw [one_mul]; exact Real.rpow_nonneg hd _
  simp only [gammaFullDeterministic, Set.mem_ofPred_eq] at hp
  rcases hp with h | h | h | h | h | ⟨k, h⟩ | ⟨k, h⟩ | ⟨k, h⟩
  · rw [gammaFull_entry_fixed g (Or.inl h) hne]; simpa using hpos
  · rw [gammaFull_entry_fixed g (Or.inr (Or.inl h)) hne]; simpa using hpos
  · rw [gammaFull_entry_fixed g (Or.inr (Or.inr (Or.inl h))) hne]; simpa using hpos
  · rw [gammaFull_entry_fixed g (Or.inr (Or.inr (Or.inr (Or.inl h)))) hne]; simpa using hpos
  · rw [gammaFull_entry_fixed g (Or.inr (Or.inr (Or.inr (Or.inr h)))) hne]; simpa using hpos
  · subst h
    obtain ⟨h1, h2⟩ := gammaFull_entry_x g k j hne
    by_cases hj : j = Symbol.one
    · subst hj
      rw [h1 rfl, homogeneity_x_sub_one, Real.rpow_one, one_mul]
      exact hg k
    · rw [h2 hj]; simpa using hpos
  · subst h
    obtain ⟨h1, h2⟩ := gammaFull_entry_psiX g k j hne
    by_cases hj : j = Symbol.psi
    · subst hj
      rw [h1 rfl, homogeneity_psiX_sub_psi, Real.rpow_one, one_mul]
      exact hg k
    · rw [h2 hj]; simpa using hpos
  · subst h
    obtain ⟨h1, h2⟩ := gammaFull_entry_psiSqX g k j hne
    by_cases hj : j = Symbol.psiSq
    · subst hj
      rw [h1 rfl, homogeneity_psiSqX_sub_psiSq, Real.rpow_one, one_mul]
      exact hg k
    · rw [h2 hj]; simpa using hpos

/-- **The deterministic entries depend on the shift only.** -/
theorem structureGroupMap_entry_eq_of_mem_gammaFullDeterministic (g g' : G)
    (hg : ∀ k : Fin 3, g.shift k.succ = g'.shift k.succ) {i j : Symbol}
    (hp : (i, j) ∈ gammaFullDeterministic) (hne : j ≠ i) :
    structureGroupMap g (basis i) j = structureGroupMap g' (basis i) j := by
  simp only [gammaFullDeterministic, Set.mem_ofPred_eq] at hp
  rcases hp with h | h | h | h | h | ⟨k, h⟩ | ⟨k, h⟩ | ⟨k, h⟩
  · rw [gammaFull_entry_fixed g (Or.inl h) hne, gammaFull_entry_fixed g' (Or.inl h) hne]
  · rw [gammaFull_entry_fixed g (Or.inr (Or.inl h)) hne,
      gammaFull_entry_fixed g' (Or.inr (Or.inl h)) hne]
  · rw [gammaFull_entry_fixed g (Or.inr (Or.inr (Or.inl h))) hne,
      gammaFull_entry_fixed g' (Or.inr (Or.inr (Or.inl h))) hne]
  · rw [gammaFull_entry_fixed g (Or.inr (Or.inr (Or.inr (Or.inl h)))) hne,
      gammaFull_entry_fixed g' (Or.inr (Or.inr (Or.inr (Or.inl h)))) hne]
  · rw [gammaFull_entry_fixed g (Or.inr (Or.inr (Or.inr (Or.inr h)))) hne,
      gammaFull_entry_fixed g' (Or.inr (Or.inr (Or.inr (Or.inr h)))) hne]
  · subst h
    obtain ⟨h1, h2⟩ := gammaFull_entry_x g k j hne
    obtain ⟨h1', h2'⟩ := gammaFull_entry_x g' k j hne
    by_cases hj : j = Symbol.one
    · rw [h1 hj, h1' hj, hg k]
    · rw [h2 hj, h2' hj]
  · subst h
    obtain ⟨h1, h2⟩ := gammaFull_entry_psiX g k j hne
    obtain ⟨h1', h2'⟩ := gammaFull_entry_psiX g' k j hne
    by_cases hj : j = Symbol.psi
    · rw [h1 hj, h1' hj, hg k]
    · rw [h2 hj, h2' hj]
  · subst h
    obtain ⟨h1, h2⟩ := gammaFull_entry_psiSqX g k j hne
    obtain ⟨h1', h2'⟩ := gammaFull_entry_psiSqX g' k j hne
    by_cases hj : j = Symbol.psiSq
    · rw [h1 hj, h1' hj, hg k]
    · rw [h2 hj, h2' hj]

end RegularityStructures.Phi43

end
