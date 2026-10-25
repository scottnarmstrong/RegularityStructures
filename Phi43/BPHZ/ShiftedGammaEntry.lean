/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullEntryMoment
import Mathlib.Tactic

/-!
# The random `Γ`-entries from parameter moments

For a random structure-group parameter `g : Ω → G` whose five components `cPsi`, `cPsiGrad k`,
`cPsiSq`, `cPsiCube` and `cPsiCube²` have the moment bounds at their gap exponents (with
`d = d(y, x)`), every off-diagonal entry `structureGroupMap (g ω) (basis i) j` of the nine
random symbols has the moment `C₀ d^(deg i - deg j + κ̄)` (`gammaShift_entry_lintegral_le`). The
parameter bounds are hypotheses, so the result applies to the canonical models with shifted
constants.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Entry moments from parameter moments.** -/
theorem gammaShift_entry_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {q : ℕ}
    (hq : 1 ≤ q) {κ : Kappa} {κbar d C1 Cg C2 C3 C4 : ℝ} (hd0 : 0 ≤ d) (g : Ω → G)
    (b1 : ∫⁻ ω, ‖(g ω).cPsi‖ₑ ^ q ∂P ≤ ENNReal.ofReal (C1 * d ^ (3 / 2 - κ.1 + κbar)) ^ q)
    (bg : ∀ k : Fin 3, ∫⁻ ω, ‖(g ω).cPsiGrad k‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (Cg * d ^ (1 / 2 - κ.1 + κbar)) ^ q)
    (b2 : ∫⁻ ω, ‖(g ω).cPsiSq‖ₑ ^ q ∂P ≤ ENNReal.ofReal (C2 * d ^ (1 - 2 * κ.1 + κbar)) ^ q)
    (b3 : ∫⁻ ω, ‖(g ω).cPsiCube‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C3 * d ^ (1 / 2 - 3 * κ.1 + κbar)) ^ q)
    (b4 : ∫⁻ ω, ‖(g ω).cPsiCube * (g ω).cPsiCube‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C4 * d ^ (1 - 6 * κ.1 + κbar)) ^ q)
    (i j : Symbol) (hi : IsGammaFullRandom i) (hj : j ≠ i) :
    ∫⁻ ω, ‖structureGroupMap (g ω) (basis i) j‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (max (max C1 Cg) (max (max C2 (2 * C3)) (max C3 C4)) *
        d ^ (homogeneity κ i - homogeneity κ j + κbar)) ^ q := by
  set C₀ := max (max C1 Cg) (max (max C2 (2 * C3)) (max C3 C4)) with hC₀
  have l1 : C1 ≤ C₀ := (le_max_left _ _).trans (le_max_left _ _)
  have lg : Cg ≤ C₀ := (le_max_right _ _).trans (le_max_left _ _)
  have l2 : C2 ≤ C₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have l23 : 2 * C3 ≤ C₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have l3 : C3 ≤ C₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have l4 : C4 ≤ C₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have zero : ∀ (e : ℝ), (∀ ω, structureGroupMap (g ω) (basis i) j = 0) →
      ∫⁻ ω, ‖structureGroupMap (g ω) (basis i) j‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C₀ * d ^ e) ^ q :=
    fun e h => lintegral_enorm_pow_of_eq_zero hq h _
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- I(Ψ²)
    by_cases h : j = Symbol.one
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiSq) Symbol.one = (g ω).cPsiSq :=
        fun ω => (gammaFull_entry_iPsiSq (g ω) _ hj).1 rfl
      simp only [e]
      exact gammaFull_bound_of_param b2 l2 hd0 (by simp only [homogeneity]; ring)
    · exact zero _ fun ω => (gammaFull_entry_iPsiSq (g ω) _ hj).2 h
  · -- I(Ψ³)
    by_cases h : j = Symbol.one
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiCube) Symbol.one =
          (g ω).cPsiCube := fun ω => (gammaFull_entry_iPsiCube (g ω) _ hj).1 rfl
      simp only [e]
      exact gammaFull_bound_of_param b3 l3 hd0 (by simp only [homogeneity]; ring)
    · exact zero _ fun ω => (gammaFull_entry_iPsiCube (g ω) _ hj).2 h
  · -- I(Ψ)Ψ
    by_cases h : j = Symbol.psi
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiPsi) Symbol.psi = (g ω).cPsi :=
        fun ω => (gammaFull_entry_iPsiPsi (g ω) _ hj).1 rfl
      simp only [e]
      exact gammaFull_bound_of_param b1 l1 hd0 (by simp only [homogeneity]; ring)
    · by_cases hk : ∃ k, j = Symbol.psiX k
      · obtain ⟨k, rfl⟩ := hk
        have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiPsi) (Symbol.psiX k) =
            (g ω).cPsiGrad k := fun ω => (gammaFull_entry_iPsiPsi (g ω) _ hj).2.1 k rfl
        simp only [e]
        exact gammaFull_bound_of_param (bg k) lg hd0 (by simp only [homogeneity]; ring)
      · push Not at hk
        exact zero _ fun ω => (gammaFull_entry_iPsiPsi (g ω) _ hj).2.2 ⟨h, hk⟩
  · -- I(Ψ)Ψ²
    by_cases h : j = Symbol.psiSq
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiPsiSq) Symbol.psiSq =
          (g ω).cPsi := fun ω => (gammaFull_entry_iPsiPsiSq (g ω) _ hj).1 rfl
      simp only [e]
      exact gammaFull_bound_of_param b1 l1 hd0 (by simp only [homogeneity]; ring)
    · by_cases hk : ∃ k, j = Symbol.psiSqX k
      · obtain ⟨k, rfl⟩ := hk
        have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiPsiSq) (Symbol.psiSqX k) =
            (g ω).cPsiGrad k := fun ω => (gammaFull_entry_iPsiPsiSq (g ω) _ hj).2.1 k rfl
        simp only [e]
        exact gammaFull_bound_of_param (bg k) lg hd0 (by simp only [homogeneity]; ring)
      · push Not at hk
        exact zero _ fun ω => (gammaFull_entry_iPsiPsiSq (g ω) _ hj).2.2 ⟨h, hk⟩
  · -- I(Ψ²)Ψ
    by_cases h : j = Symbol.psi
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiSqPsi) Symbol.psi =
          (g ω).cPsiSq := fun ω => (gammaFull_entry_iPsiSqPsi (g ω) _ hj).1 rfl
      simp only [e]
      exact gammaFull_bound_of_param b2 l2 hd0 (by simp only [homogeneity]; ring)
    · exact zero _ fun ω => (gammaFull_entry_iPsiSqPsi (g ω) _ hj).2 h
  · -- I(Ψ²)Ψ²
    by_cases h : j = Symbol.psiSq
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiSqPsiSq) Symbol.psiSq =
          (g ω).cPsiSq := fun ω => (gammaFull_entry_iPsiSqPsiSq (g ω) _ hj).1 rfl
      simp only [e]
      exact gammaFull_bound_of_param b2 l2 hd0 (by simp only [homogeneity]; ring)
    · exact zero _ fun ω => (gammaFull_entry_iPsiSqPsiSq (g ω) _ hj).2 h
  · -- I(Ψ³)Ψ
    by_cases h : j = Symbol.psi
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiCubePsi) Symbol.psi =
          (g ω).cPsiCube := fun ω => (gammaFull_entry_iPsiCubePsi (g ω) _ hj).1 rfl
      simp only [e]
      exact gammaFull_bound_of_param b3 l3 hd0 (by simp only [homogeneity]; ring)
    · exact zero _ fun ω => (gammaFull_entry_iPsiCubePsi (g ω) _ hj).2 h
  · -- I(Ψ³)Ψ²
    by_cases h : j = Symbol.psiSq
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiCubePsiSq) Symbol.psiSq =
          (g ω).cPsiCube := fun ω => (gammaFull_entry_iPsiCubePsiSq (g ω) _ hj).1 rfl
      simp only [e]
      exact gammaFull_bound_of_param b3 l3 hd0 (by simp only [homogeneity]; ring)
    · exact zero _ fun ω => (gammaFull_entry_iPsiCubePsiSq (g ω) _ hj).2 h
  · -- I(Ψ³)²
    by_cases h : j = Symbol.iPsiCube
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiCubeSq) Symbol.iPsiCube =
          2 * (g ω).cPsiCube := fun ω => (gammaFull_entry_iPsiCubeSq (g ω) _ hj).1 rfl
      simp only [e]
      refine gammaFull_bound_of_param (a := 2 * C3) (E := 1 / 2 - 3 * κ.1 + κbar) ?_ l23 hd0 (by simp only [homogeneity]; ring)
      refine le_ofReal_pow_mono (lintegral_enorm_pow_const_mul_le 2 b3) ?_
      rw [abs_two]
      exact le_of_eq (by ring)
    · by_cases h' : j = Symbol.one
      · subst h'
        have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiCubeSq) Symbol.one =
            (g ω).cPsiCube * (g ω).cPsiCube :=
          fun ω => (gammaFull_entry_iPsiCubeSq (g ω) _ hj).2.1 rfl
        simp only [e]
        exact gammaFull_bound_of_param b4 l4 hd0 (by simp only [homogeneity]; ring)
      · exact zero _ fun ω => (gammaFull_entry_iPsiCubeSq (g ω) _ hj).2.2 ⟨h, h'⟩

end RegularityStructures.Phi43

end
