/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PsiGaussianVector
public import Phi43.BPHZ.TreePsiMoment
public import RegularityStructures.BPHZ.GaussianWickMonomialSpecial
public import RegularityStructures.Probability.Isserlis

/-!
# The Wick square of the tree `Ψ`

With `Q_ε = hairerCovariance N ρ ε` and `c_ε = hairerWickConstant N ρ ε = Q_ε(0)`, the Wick square
`:Ψ²:(z) = Ψ(z)² - c_ε` satisfies `E[:Ψ²:(u) :Ψ²:(v)] = 2 Q_ε(u - v)²`.  The proof applies the
Gaussian vector `(Ψ(u), Ψ(v))` and the formula for the covariance of Wick squares; the Wick square
is `wickMonomial C [0, 0]` of that vector (`wickMonomial_pair_self`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The Wick square `Ψ(z)² - c_ε` of the tree `Ψ`. -/
def hairerPsiWickSquare {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (ω : Ω) (z : SpaceTime) : ℝ :=
  hairerPsiField N ξ ω z ^ 2 - hairerWickConstant N ρ ε

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The Wick constant is the covariance at the origin: `c_ε = Q_ε(0)`. -/
theorem hairerWickConstant_eq_covariance_zero (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) :
    hairerWickConstant N ρ ε = hairerCovariance N ρ ε 0 := by
  unfold hairerWickConstant hairerCovariance
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [sq]

/-- The tree `Ψ` at a fixed point is measurable in `ω`. -/
theorem measurable_hairerPsiField_apply (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (z : SpaceTime) : Measurable fun ω => hairerPsiField N ξ ω z := by
  have hj := measurable_hairerPsiField_uncurry N hξ
  have hz : Measurable fun ω : Ω => (ω, z) := measurable_id.prodMk measurable_const
  exact Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiField N ξ q.1 q.2)
    (f := fun ω : Ω => (ω, z)) hj hz

/-- The Wick square of `Ψ` is jointly measurable. -/
theorem measurable_hairerPsiWickSquare_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    Measurable (fun q : Ω × SpaceTime => hairerPsiWickSquare N ρ ε ξ q.1 q.2) :=
  ((measurable_hairerPsiField_uncurry N hξ).pow_const 2).sub_const _

/-- **Covariance of the Wick square of `Ψ`.** `E[:Ψ²:(u) :Ψ²:(v)] = 2 Q_ε(u - v)²`. -/
theorem hairerPsiWickSquare_integral_mul (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (u v : SpaceTime) :
    ∫ ω, hairerPsiWickSquare N ρ ε ξ ω u * hairerPsiWickSquare N ρ ε ξ ω v ∂P =
      2 * hairerCovariance N ρ ε (u - v) ^ 2 := by
  have h := hairerPsiField_isCentredGaussianVector N hρ hε hW hξ ![u, v]
  have h2 := h.integral_sq_sub_mul_sq_sub 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self] at h2
  simp only [hairerPsiWickSquare, hairerWickConstant_eq_covariance_zero]
  convert h2 using 3

/-- The Wick square of `Ψ` is square integrable. -/
theorem hairerPsiWickSquare_memLp (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    MemLp (fun ω => hairerPsiWickSquare N ρ ε ξ ω z) 2 P := by
  have h := hairerPsiField_isCentredGaussianVector N hρ hε hW hξ ![z]
  have hi := h.integrable_sq_sub_mul_sq_sub 0 0 (hairerCovariance N ρ ε 0)
    (hairerCovariance N ρ ε 0)
  have hm : Measurable fun ω => hairerPsiWickSquare N ρ ε ξ ω z :=
    ((measurable_hairerPsiField_apply N hξ z).pow_const 2).sub_const _
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  simp only [hairerPsiWickSquare, hairerWickConstant_eq_covariance_zero]
  simpa [sq] using hi

end RegularityStructures.Phi43

end
