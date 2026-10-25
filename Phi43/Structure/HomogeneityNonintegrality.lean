/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.Symbols
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Non-integrality of the degrees of the retained finite structure

Hairer [Hai14, Assumption 5.3] for the retained finite structure.
Every retained non-polynomial degree lies strictly between successive
integers for `0 < κ < 1/16`. This statement excludes all polynomial symbols
explicitly and does not assert non-integrality for a larger tree structure.

In particular, the unretained cubic `I(Ψ³)^3` has degree `3/2 - 9κ` and
resonates at `κ = 1/18`; this resonance is checked separately below.
-/

public section

namespace RegularityStructures.Phi43

private theorem ne_int_of_between {x : ℝ} (m n : ℤ)
    (h0 : (m : ℝ) < x) (h1 : x < (m : ℝ) + 1) : x ≠ (n : ℝ) := by
  intro he
  rw [he] at h0 h1
  have hn0 : m < n := by exact_mod_cast h0
  have hn1 : n < m + 1 := by exact_mod_cast h1
  omega

/-- No additional excluded kappa values are needed for the current retained
NON-polynomial type. This does not assert anything about unretained trees. -/
theorem phi43_nonpolynomial_homogeneity_ne_int (κ : Kappa) (τ : Symbol)
    (hτ : τ ≠ .one) (hτ0 : τ ≠ .x0)
    (hτx : ∀ i, τ ≠ .x i) (hτxx : ∀ p, τ ≠ .xMul p) (n : ℤ) :
    homogeneity κ τ ≠ (n : ℝ) := by
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  cases τ with
  | one => exact False.elim (hτ rfl)
  | x0 => exact False.elim (hτ0 rfl)
  | x i => exact False.elim (hτx i rfl)
  | xMul p => exact False.elim (hτxx p rfl)
  | noise =>
      apply ne_int_of_between (-3) n <;> norm_num [homogeneity] <;> linarith
  | psi =>
      apply ne_int_of_between (-1) n <;> norm_num [homogeneity] <;> linarith
  | iPsi =>
      apply ne_int_of_between 1 n <;> norm_num [homogeneity] <;> linarith
  | psiSq =>
      apply ne_int_of_between (-2) n <;> norm_num [homogeneity] <;> linarith
  | psiCube =>
      apply ne_int_of_between (-2) n <;> norm_num [homogeneity] <;> linarith
  | psiX i =>
      apply ne_int_of_between 0 n <;> norm_num [homogeneity] <;> linarith
  | psiSqX i =>
      apply ne_int_of_between (-1) n <;> norm_num [homogeneity] <;> linarith
  | iPsiSq =>
      apply ne_int_of_between 0 n <;> norm_num [homogeneity] <;> linarith
  | iPsiCube =>
      apply ne_int_of_between 0 n <;> norm_num [homogeneity] <;> linarith
  | iPsiPsi =>
      apply ne_int_of_between 0 n <;> norm_num [homogeneity] <;> linarith
  | iPsiPsiSq =>
      apply ne_int_of_between 0 n <;> norm_num [homogeneity] <;> linarith
  | iPsiSqPsi =>
      apply ne_int_of_between 0 n <;> norm_num [homogeneity] <;> linarith
  | iPsiSqPsiSq =>
      apply ne_int_of_between (-1) n <;> norm_num [homogeneity] <;> linarith
  | iPsiCubePsi =>
      apply ne_int_of_between (-1) n <;> norm_num [homogeneity] <;> linarith
  | iPsiCubePsiSq =>
      apply ne_int_of_between (-1) n <;> norm_num [homogeneity] <;> linarith
  | iPsiCubeSq =>
      apply ne_int_of_between 0 n <;> norm_num [homogeneity] <;> linarith

end RegularityStructures.Phi43

end
