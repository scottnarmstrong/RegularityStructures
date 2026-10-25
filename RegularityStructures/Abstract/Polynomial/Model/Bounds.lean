/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Reg

/-!
# The `Π` bound for the polynomial regularisations

`abs_polyReg_single_le`: `|(Q_t (· - x)^k)(x)| ≤ M_{|k|_𝔰} t^{|k|_𝔰/4}`, from
`|∫ q_t(x - z) (z - x)^k dz| ≤ ∫ |q_t(x - z)| ‖z - x‖_𝔰^{|k|_𝔰} dz` and the moment bounds. This is
the `Π` bound of the polynomial model `Π_x X^k = (· - x)^k`; `polyPiConst N` bounds the constants
uniformly in `|k|_𝔰 < N`.

[Hai14, Definition 2.1 (2.15), Remark 2.23 and (2.21)].
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {N : ℕ}

/-- The constant `∑ₖ M_{|k|_𝔰}`, depending only on `N`, which dominates the constants of
`abs_polyReg_single_le` for `|k|_𝔰 < N`. -/
@[expose] noncomputable def polyPiConst (N : ℕ) : ℝ := ∑ k : PolyIndex N, parabolicMomentConst (polyDeg N k)

theorem abs_polyReg_single_le (k : PolyIndex N) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    |polyReg x (Pi.single k 1) t x| ≤ parabolicMomentConst (polyDeg N k) * t ^ (polyDeg N k / 4) := by
  have hr : 0 ≤ polyDeg N k := Nat.cast_nonneg _
  rw [polyReg_of_pos x _ ht]
  have hint := integrable_parabolicKernel_mul_polyEval x (Pi.single k 1) ht x
  calc |parabolicSemigroup.apply t (polyEval x (Pi.single k 1)) x|
      ≤ ∫ z, |parabolicKernel t (x - z) * polyEval x (Pi.single k 1) z| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, |parabolicSemigroup.kernel t x z| * parabolicSemigroup.scaleDist z x ^ (polyDeg N k) := by
        refine integral_mono hint.abs (parabolicSemigroup.integrable_moment ht hr x) fun z => ?_
        rw [abs_mul, polyEval_single]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (abs_evalParabolic_monomial_le _ _).trans ?_
        have : polyDeg N k = ((2 * k.1 0 + k.1 1 + k.1 2 + k.1 3 : ℕ) : ℝ) := by
          simp only [polyDeg, weight_parabolicWeight]
        rw [this, Real.rpow_natCast]
        rfl
    _ ≤ _ := parabolicSemigroup.moment_le ht hr x

end RegularityStructures

end
