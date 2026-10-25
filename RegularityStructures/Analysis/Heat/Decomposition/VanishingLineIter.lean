/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Vanishing
public import RegularityStructures.Analysis.Heat.Decomposition.Scaling
public import RegularityStructures.Analysis.Heat.Decomposition.ScalingDeriv

/-!
# Vanishing moments of derivatives

`integral_monoFn_mul_lineIter_eq_zero`: for `g` smooth with compact support,
`∫ z^l D^J g(z) dz = 0` whenever `l_i` is smaller than the number of derivatives in the direction
`i` for some `i` (integration by parts).
-/

@[expose] public noncomputable section

namespace RegularityStructures

end RegularityStructures

end

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem integral_monoFn_mul_lineIter_eq_zero {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (J : List (Fin 4)) :
    ∀ l : Fin 4 → ℕ, (∃ i, l i < J.count i) →
      ∫ z, monoFn l z * lineIter (J.map coordDir) g z = 0 := by
  induction J with
  | nil => rintro l ⟨i, hi⟩; simp at hi
  | cons j J ih =>
    rintro l ⟨i, hi⟩
    have hG := contDiff_lineIter hg (J.map coordDir)
    have hGc := hasCompactSupport_lineIter hc (J.map coordDir)
    simp only [List.map_cons, lineIter_cons]
    have hibp := integral_dirDeriv_mul (coordDir j) (contDiff_monoFn l) hG hGc
    by_cases hl : l j = 0
    · have : dirDeriv (coordDir j) (monoFn l) = 0 := by
        rw [dirDeriv_coordDir_monoFn]; funext z; simp [hl]
      rw [this] at hibp
      simp only [Pi.zero_apply, zero_mul, integral_zero] at hibp
      have := hibp.symm
      rw [neg_eq_zero] at this
      exact this
    · have hnew : ∃ i', Function.update l j (l j - 1) i' < J.count i' := by
        by_cases hij : i = j
        · subst hij
          refine ⟨i, ?_⟩
          rw [Function.update_self]
          rw [List.count_cons_self] at hi
          omega
        · refine ⟨i, ?_⟩
          rw [Function.update_of_ne hij]
          rwa [List.count_cons_of_ne (Ne.symm hij)] at hi
      have h0 := ih _ hnew
      rw [dirDeriv_coordDir_monoFn] at hibp
      have : ∫ z, (l j : ℝ) * monoFn (Function.update l j (l j - 1)) z *
          lineIter (J.map coordDir) g z = 0 := by
        simp_rw [mul_assoc]
        rw [integral_const_mul, h0, mul_zero]
      rw [this] at hibp
      simpa using hibp.symm

end RegularityStructures

end
