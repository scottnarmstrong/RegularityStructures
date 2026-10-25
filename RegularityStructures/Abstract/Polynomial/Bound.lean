/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Structure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import RegularityStructures.Abstract.RegularityStructureDegrees

/-!
# The bound on the translations

The coefficient of `X^l` in `(X + h)^k` is `binom(k, l) h^{k-l}`, bounded by
`C ‖h‖_𝔰^{|k|_𝔰 - |l|_𝔰}` (`polyTranslate_single_le`), which is the bound
`|Γ_{xy} τ|_ℓ ≲ ‖x - y‖_𝔰^{|τ| - ℓ}` on the structure group [Hai14, Definition 2.1, (2.21)].
-/

public section

namespace RegularityStructures

variable {N : ℕ}

theorem prod_choose_le (k l : Fin 4 →₀ ℕ) (hk : ∀ i, k i < N) :
    ∏ i, ((k i).choose (l i) : ℝ) ≤ 2 ^ (4 * N) := by
  calc ∏ i, ((k i).choose (l i) : ℝ) ≤ ∏ _i : Fin 4, (2 : ℝ) ^ N := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => ?_
        have : (k i).choose (l i) ≤ 2 ^ N :=
          (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (hk i).le)
        exact_mod_cast this
    _ = 2 ^ (4 * N) := by simp [pow_mul']

/-- The coefficient of `X^l` in `(X + h)^k`, `|l|_𝔰 < |k|_𝔰`, is bounded by `C ‖h‖_𝔰^{|k|_𝔰 - |l|_𝔰}`
with `C` depending only on `N`. -/
theorem polyTranslate_single_le (N : ℕ) :
    ∃ C : ℝ, ∀ (h : ParabolicSpace) (k l : PolyIndex N), polyDeg N l < polyDeg N k →
      |polyTranslate (parabolicCoords h) (Pi.single k 1) l| ≤
        C * parabolicNorm h ^ (polyDeg N k - polyDeg N l) := by
  refine ⟨2 ^ (4 * N), fun h k l _ => ?_⟩
  have hn := parabolicNorm_nonneg h
  rw [polyTranslate_single_apply]
  by_cases hle : l.1 ≤ k.1
  · simp only [hle, ↓reduceIte]
    have hli := Finsupp.le_def.1 hle
    have hnat : Finsupp.weight parabolicWeight k.1 = Finsupp.weight parabolicWeight l.1 +
        (2 * (k.1 - l.1) 0 + (k.1 - l.1) 1 + (k.1 - l.1) 2 + (k.1 - l.1) 3) := by
      rw [weight_parabolicWeight, weight_parabolicWeight]
      simp only [Finsupp.tsub_apply]
      have h0 := hli 0
      have h1 := hli 1
      have h2 := hli 2
      have h3 := hli 3
      omega
    have hexp : polyDeg N k - polyDeg N l =
        ((2 * (k.1 - l.1) 0 + (k.1 - l.1) 1 + (k.1 - l.1) 2 + (k.1 - l.1) 3 : ℕ) : ℝ) := by
      have := congrArg (Nat.cast (R := ℝ)) hnat
      simp only [polyDeg]
      push_cast at this ⊢
      linarith
    rw [hexp, Real.rpow_natCast, Finset.prod_mul_distrib, abs_mul]
    have hmono : ∏ i, parabolicCoords h i ^ (k.1 i - l.1 i) =
        evalParabolic (MvPolynomial.monomial (k.1 - l.1) 1) h := by
      simp [evalParabolic, MvPolynomial.eval_monomial, Finsupp.prod_fintype]
    have hch : |∏ i, ((k.1 i).choose (l.1 i) : ℝ)| ≤ 2 ^ (4 * N) := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
      exact prod_choose_le _ _ (coord_lt_of_weight_lt k.2)
    rw [hmono, mul_comm]
    exact mul_le_mul hch (abs_evalParabolic_monomial_le _ _) (abs_nonneg _) (by positivity)
  · simp only [hle, ↓reduceIte, abs_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hn _)

end RegularityStructures

end
