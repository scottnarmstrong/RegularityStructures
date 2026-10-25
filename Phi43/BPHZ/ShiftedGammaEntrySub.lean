/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedGammaEntry
public import Phi43.BPHZ.GammaFullEntryMomentSub
import Mathlib.Tactic

/-!
# Differences of the random `Γ`-entries from parameter moments

For two random structure-group parameters `g g' : Ω → G` whose component differences have the
moment bounds `C M d^gap` (`M ≥ 0` the difference factor, `d = d(y, x)`), the entries
`structureGroupMap (g ω) (basis i) j - structureGroupMap (g' ω) (basis i) j` of the nine random
symbols have the moment `C₀ M d^(deg i - deg j + κ̄)` (`gammaShift_entry_sub_lintegral_le`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Entry difference moments from parameter difference moments.** -/
theorem gammaShift_entry_sub_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℕ} (hq : 1 ≤ q) {κ : Kappa} {κbar d M C1 Cg C2 C3 C4 : ℝ} (hd0 : 0 ≤ d) (hM : 0 ≤ M)
    (g g' : Ω → G)
    (b1 : ∫⁻ ω, ‖(g ω).cPsi - (g' ω).cPsi‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C1 * M * d ^ (3 / 2 - κ.1 + κbar)) ^ q)
    (bg : ∀ k : Fin 3, ∫⁻ ω, ‖(g ω).cPsiGrad k - (g' ω).cPsiGrad k‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (Cg * M * d ^ (1 / 2 - κ.1 + κbar)) ^ q)
    (b2 : ∫⁻ ω, ‖(g ω).cPsiSq - (g' ω).cPsiSq‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C2 * M * d ^ (1 - 2 * κ.1 + κbar)) ^ q)
    (b3 : ∫⁻ ω, ‖(g ω).cPsiCube - (g' ω).cPsiCube‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C3 * M * d ^ (1 / 2 - 3 * κ.1 + κbar)) ^ q)
    (b4 : ∫⁻ ω, ‖(g ω).cPsiCube * (g ω).cPsiCube -
        (g' ω).cPsiCube * (g' ω).cPsiCube‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C4 * M * d ^ (1 - 6 * κ.1 + κbar)) ^ q)
    (i j : Symbol) (hi : IsGammaFullRandom i) (hj : j ≠ i) :
    ∫⁻ ω, ‖structureGroupMap (g ω) (basis i) j - structureGroupMap (g' ω) (basis i) j‖ₑ ^ q
        ∂P ≤
      ENNReal.ofReal (max (max C1 Cg) (max (max C2 (2 * C3)) (max C3 C4)) * M *
        d ^ (homogeneity κ i - homogeneity κ j + κbar)) ^ q := by
  set C₀ := max (max C1 Cg) (max (max C2 (2 * C3)) (max C3 C4)) with hC₀
  have l1 : C1 ≤ C₀ := (le_max_left _ _).trans (le_max_left _ _)
  have lg : Cg ≤ C₀ := (le_max_right _ _).trans (le_max_left _ _)
  have l2 : C2 ≤ C₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have l23 : 2 * C3 ≤ C₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have l3 : C3 ≤ C₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have l4 : C4 ≤ C₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have zero : ∀ (e : ℝ),
      (∀ ω, structureGroupMap (g ω) (basis i) j = 0) →
      (∀ ω, structureGroupMap (g' ω) (basis i) j = 0) →
      ∫⁻ ω, ‖structureGroupMap (g ω) (basis i) j - structureGroupMap (g' ω) (basis i) j‖ₑ ^ q
          ∂P ≤ ENNReal.ofReal (C₀ * M * d ^ e) ^ q :=
    fun e h h' => lintegral_enorm_pow_of_eq_zero hq (fun ω => by rw [h ω, h' ω, sub_zero]) _
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- I(Ψ²)
    by_cases h : j = Symbol.one
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiSq)
          Symbol.one = (g ω).cPsiSq :=
        fun ω => (gammaFull_entry_iPsiSq _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω) (basis Symbol.iPsiSq)
          Symbol.one = (g' ω).cPsiSq :=
        fun ω => (gammaFull_entry_iPsiSq _ _ hj).1 rfl
      simp only [e, e']
      exact gammaFull_bound_of_param_sub b2 l2 hM hd0 (by simp only [homogeneity]; ring)
    · exact zero _ (fun ω => (gammaFull_entry_iPsiSq _ _ hj).2 h)
        (fun ω => (gammaFull_entry_iPsiSq _ _ hj).2 h)
  · -- I(Ψ³)
    by_cases h : j = Symbol.one
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiCube)
          Symbol.one = (g ω).cPsiCube :=
        fun ω => (gammaFull_entry_iPsiCube _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω) (basis Symbol.iPsiCube)
          Symbol.one = (g' ω).cPsiCube :=
        fun ω => (gammaFull_entry_iPsiCube _ _ hj).1 rfl
      simp only [e, e']
      exact gammaFull_bound_of_param_sub b3 l3 hM hd0 (by simp only [homogeneity]; ring)
    · exact zero _ (fun ω => (gammaFull_entry_iPsiCube _ _ hj).2 h)
        (fun ω => (gammaFull_entry_iPsiCube _ _ hj).2 h)
  · -- I(Ψ)Ψ
    by_cases h : j = Symbol.psi
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiPsi)
          Symbol.psi = (g ω).cPsi :=
        fun ω => (gammaFull_entry_iPsiPsi _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω) (basis Symbol.iPsiPsi)
          Symbol.psi = (g' ω).cPsi :=
        fun ω => (gammaFull_entry_iPsiPsi _ _ hj).1 rfl
      simp only [e, e']
      exact gammaFull_bound_of_param_sub b1 l1 hM hd0 (by simp only [homogeneity]; ring)
    · by_cases hk : ∃ k, j = Symbol.psiX k
      · obtain ⟨k, rfl⟩ := hk
        have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiPsi)
            (Symbol.psiX k) = (g ω).cPsiGrad k :=
          fun ω => (gammaFull_entry_iPsiPsi _ _ hj).2.1 k rfl
        have e' : ∀ ω, structureGroupMap (g' ω) (basis Symbol.iPsiPsi)
            (Symbol.psiX k) = (g' ω).cPsiGrad k :=
          fun ω => (gammaFull_entry_iPsiPsi _ _ hj).2.1 k rfl
        simp only [e, e']
        exact gammaFull_bound_of_param_sub (bg k) lg hM hd0 (by simp only [homogeneity]; ring)
      · push Not at hk
        exact zero _ (fun ω => (gammaFull_entry_iPsiPsi _ _ hj).2.2 ⟨h, hk⟩)
          (fun ω => (gammaFull_entry_iPsiPsi _ _ hj).2.2 ⟨h, hk⟩)
  · -- I(Ψ)Ψ²
    by_cases h : j = Symbol.psiSq
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiPsiSq)
          Symbol.psiSq = (g ω).cPsi :=
        fun ω => (gammaFull_entry_iPsiPsiSq _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω)
          (basis Symbol.iPsiPsiSq) Symbol.psiSq = (g' ω).cPsi :=
        fun ω => (gammaFull_entry_iPsiPsiSq _ _ hj).1 rfl
      simp only [e, e']
      exact gammaFull_bound_of_param_sub b1 l1 hM hd0 (by simp only [homogeneity]; ring)
    · by_cases hk : ∃ k, j = Symbol.psiSqX k
      · obtain ⟨k, rfl⟩ := hk
        have e : ∀ ω, structureGroupMap (g ω)
            (basis Symbol.iPsiPsiSq) (Symbol.psiSqX k) =
            (g ω).cPsiGrad k :=
          fun ω => (gammaFull_entry_iPsiPsiSq _ _ hj).2.1 k rfl
        have e' : ∀ ω, structureGroupMap (g' ω)
            (basis Symbol.iPsiPsiSq) (Symbol.psiSqX k) =
            (g' ω).cPsiGrad k :=
          fun ω => (gammaFull_entry_iPsiPsiSq _ _ hj).2.1 k rfl
        simp only [e, e']
        exact gammaFull_bound_of_param_sub (bg k) lg hM hd0 (by simp only [homogeneity]; ring)
      · push Not at hk
        exact zero _ (fun ω => (gammaFull_entry_iPsiPsiSq _ _ hj).2.2 ⟨h, hk⟩)
          (fun ω => (gammaFull_entry_iPsiPsiSq _ _ hj).2.2 ⟨h, hk⟩)
  · -- I(Ψ²)Ψ
    by_cases h : j = Symbol.psi
    · subst h
      have e : ∀ ω, structureGroupMap (g ω) (basis Symbol.iPsiSqPsi)
          Symbol.psi = (g ω).cPsiSq :=
        fun ω => (gammaFull_entry_iPsiSqPsi _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω)
          (basis Symbol.iPsiSqPsi) Symbol.psi = (g' ω).cPsiSq :=
        fun ω => (gammaFull_entry_iPsiSqPsi _ _ hj).1 rfl
      simp only [e, e']
      exact gammaFull_bound_of_param_sub b2 l2 hM hd0 (by simp only [homogeneity]; ring)
    · exact zero _ (fun ω => (gammaFull_entry_iPsiSqPsi _ _ hj).2 h)
        (fun ω => (gammaFull_entry_iPsiSqPsi _ _ hj).2 h)
  · -- I(Ψ²)Ψ²
    by_cases h : j = Symbol.psiSq
    · subst h
      have e : ∀ ω, structureGroupMap (g ω)
          (basis Symbol.iPsiSqPsiSq) Symbol.psiSq = (g ω).cPsiSq :=
        fun ω => (gammaFull_entry_iPsiSqPsiSq _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω)
          (basis Symbol.iPsiSqPsiSq) Symbol.psiSq = (g' ω).cPsiSq :=
        fun ω => (gammaFull_entry_iPsiSqPsiSq _ _ hj).1 rfl
      simp only [e, e']
      exact gammaFull_bound_of_param_sub b2 l2 hM hd0 (by simp only [homogeneity]; ring)
    · exact zero _ (fun ω => (gammaFull_entry_iPsiSqPsiSq _ _ hj).2 h)
        (fun ω => (gammaFull_entry_iPsiSqPsiSq _ _ hj).2 h)
  · -- I(Ψ³)Ψ
    by_cases h : j = Symbol.psi
    · subst h
      have e : ∀ ω, structureGroupMap (g ω)
          (basis Symbol.iPsiCubePsi) Symbol.psi = (g ω).cPsiCube :=
        fun ω => (gammaFull_entry_iPsiCubePsi _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω)
          (basis Symbol.iPsiCubePsi) Symbol.psi = (g' ω).cPsiCube :=
        fun ω => (gammaFull_entry_iPsiCubePsi _ _ hj).1 rfl
      simp only [e, e']
      exact gammaFull_bound_of_param_sub b3 l3 hM hd0 (by simp only [homogeneity]; ring)
    · exact zero _ (fun ω => (gammaFull_entry_iPsiCubePsi _ _ hj).2 h)
        (fun ω => (gammaFull_entry_iPsiCubePsi _ _ hj).2 h)
  · -- I(Ψ³)Ψ²
    by_cases h : j = Symbol.psiSq
    · subst h
      have e : ∀ ω, structureGroupMap (g ω)
          (basis Symbol.iPsiCubePsiSq) Symbol.psiSq =
          (g ω).cPsiCube :=
        fun ω => (gammaFull_entry_iPsiCubePsiSq _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω)
          (basis Symbol.iPsiCubePsiSq) Symbol.psiSq =
          (g' ω).cPsiCube :=
        fun ω => (gammaFull_entry_iPsiCubePsiSq _ _ hj).1 rfl
      simp only [e, e']
      exact gammaFull_bound_of_param_sub b3 l3 hM hd0 (by simp only [homogeneity]; ring)
    · exact zero _ (fun ω => (gammaFull_entry_iPsiCubePsiSq _ _ hj).2 h)
        (fun ω => (gammaFull_entry_iPsiCubePsiSq _ _ hj).2 h)
  · -- I(Ψ³)²
    by_cases h : j = Symbol.iPsiCube
    · subst h
      have e : ∀ ω, structureGroupMap (g ω)
          (basis Symbol.iPsiCubeSq) Symbol.iPsiCube =
          2 * (g ω).cPsiCube :=
        fun ω => (gammaFull_entry_iPsiCubeSq _ _ hj).1 rfl
      have e' : ∀ ω, structureGroupMap (g' ω)
          (basis Symbol.iPsiCubeSq) Symbol.iPsiCube =
          2 * (g' ω).cPsiCube :=
        fun ω => (gammaFull_entry_iPsiCubeSq _ _ hj).1 rfl
      simp only [e, e', ← mul_sub]
      refine gammaFull_bound_of_param_sub (a := 2 * C3) (E := 1 / 2 - 3 * κ.1 + κbar) ?_ l23 hM
        hd0 (by simp only [homogeneity]; ring)
      refine le_ofReal_pow_mono (lintegral_enorm_pow_const_mul_le 2 b3) ?_
      rw [abs_two]
      exact le_of_eq (by ring)
    · by_cases h' : j = Symbol.one
      · subst h'
        have e : ∀ ω, structureGroupMap (g ω)
            (basis Symbol.iPsiCubeSq) Symbol.one =
            (g ω).cPsiCube *
              (g ω).cPsiCube :=
          fun ω => (gammaFull_entry_iPsiCubeSq _ _ hj).2.1 rfl
        have e' : ∀ ω, structureGroupMap (g' ω)
            (basis Symbol.iPsiCubeSq) Symbol.one =
            (g' ω).cPsiCube *
              (g' ω).cPsiCube :=
          fun ω => (gammaFull_entry_iPsiCubeSq _ _ hj).2.1 rfl
        simp only [e, e']
        exact gammaFull_bound_of_param_sub b4 l4 hM hd0 (by simp only [homogeneity]; ring)
      · exact zero _ (fun ω => (gammaFull_entry_iPsiCubeSq _ _ hj).2.2 ⟨h, h'⟩)
          (fun ω => (gammaFull_entry_iPsiCubeSq _ _ hj).2.2 ⟨h, h'⟩)

end RegularityStructures.Phi43

end
