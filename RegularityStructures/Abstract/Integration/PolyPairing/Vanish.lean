/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Moment
public import RegularityStructures.Analysis.Heat.Decomposition.Regularising
public import RegularityStructures.Analysis.Kernel.GeneratorIBP
public import RegularityStructures.Abstract.Polynomial.Structure

/-!
# Derivatives of the annihilating shells annihilate low-degree monomials

If `g` is smooth with compact support and all its monomial moments `∫ z^l g` of parabolic
degree `< N` vanish, so do the moments `∫ z^l D^J g` of every iterated coordinate derivative of `g`
(integration by parts, `integral_monoFn_mul_lineIter_eq_zero_of_moments`). Applied to
`annShell N n` (`integral_monoFn_mul_lineIter_annShell_eq_zero`) and combined with the reflection
`z ↦ y - z` this gives the vanishing of `∫ (z - y)^l D^k K_n (y - z) dz` for `|l|_𝔰 < N`
(`integral_polyEval_mul_lineIter_annShell`).  [Hai14, proof of Theorem 5.12, (5.44)–(5.50)].
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

/-- The parabolic weight `∑ᵢ 𝔰ᵢ lᵢ` of a function-valued multi-index. -/
def fnWeight (l : Fin 4 → ℕ) : ℕ := ∑ i, parabolicWeight i * l i

theorem fnWeight_update_le (l : Fin 4 → ℕ) (j : Fin 4) :
    fnWeight (Function.update l j (l j - 1)) ≤ fnWeight l := by
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : i = j
  · subst h
    simp only [Function.update_self]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  · rw [Function.update_of_ne h]

theorem fnWeight_equivFunOnFinite (l : Fin 4 → ℕ) :
    Finsupp.weight parabolicWeight (Finsupp.equivFunOnFinite.symm l) = fnWeight l := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp [fnWeight, mul_comm]

theorem integral_monoFn_mul_lineIter_eq_zero_of_moments {g : ParabolicSpace → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {N : ℕ}
    (hmom : ∀ l : Fin 4 → ℕ, fnWeight l < N → ∫ z, monoFn l z * g z = 0) (J : List (Fin 4)) :
    ∀ l : Fin 4 → ℕ, fnWeight l < N → ∫ z, monoFn l z * lineIter (J.map coordDir) g z = 0 := by
  induction J with
  | nil => intro l hl; simpa [lineIter] using hmom l hl
  | cons j J ih =>
    intro l hl
    have hG := contDiff_lineIter hg (J.map coordDir)
    have hGc := hasCompactSupport_lineIter hc (J.map coordDir)
    simp only [List.map_cons, lineIter_cons]
    have hibp := integral_dirDeriv_mul (coordDir j) (contDiff_monoFn l) hG hGc
    by_cases hlj : l j = 0
    · have : dirDeriv (coordDir j) (monoFn l) = 0 := by
        rw [dirDeriv_coordDir_monoFn]; funext z; simp [hlj]
      rw [this] at hibp
      simp only [Pi.zero_apply, zero_mul, integral_zero] at hibp
      have := hibp.symm
      rwa [neg_eq_zero] at this
    · have h0 := ih _ (lt_of_le_of_lt (fnWeight_update_le l j) hl)
      rw [dirDeriv_coordDir_monoFn] at hibp
      have : ∫ z, (l j : ℝ) * monoFn (Function.update l j (l j - 1)) z *
          lineIter (J.map coordDir) g z = 0 := by
        simp_rw [mul_assoc]
        rw [integral_const_mul, h0, mul_zero]
      rw [this] at hibp
      simpa using hibp.symm

end RegularityStructures

end
