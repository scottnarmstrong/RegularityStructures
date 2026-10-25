/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickBlocksTwo
public import RegularityStructures.BPHZ.GaussianWickDiagram
public import Phi43.BPHZ.TreeWickSquare

/-!
# The Wick cube of the tree `Ψ`

With `Q_ε = hairerCovariance N ρ ε` and `c_ε = hairerWickConstant N ρ ε = Q_ε(0)`, the Wick cube
`:Ψ³:(z) = Ψ(z)³ - 3 c_ε Ψ(z)` satisfies `E[:Ψ³:(u) :Ψ³:(v)] = 6 Q_ε(u - v)³`.  The proof applies
the Gaussian vector `(Ψ(u), Ψ(v))` and the diagram formula for two Wick monomials of length `3`
(`integral_wick_replicate_mul_wick_replicate`); the Wick cube is `wickMonomial C [0, 0, 0]` of that
vector (`wickMonomial_triple_self`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The Wick cube `Ψ(z)³ - 3 c_ε Ψ(z)` of the tree `Ψ`. -/
def hairerPsiWickCube {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (ω : Ω) (z : SpaceTime) : ℝ :=
  hairerPsiField N ξ ω z ^ 3 - 3 * hairerWickConstant N ρ ε * hairerPsiField N ξ ω z

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The Wick cube of `Ψ` is jointly measurable. -/
theorem measurable_hairerPsiWickCube_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    Measurable (fun q : Ω × SpaceTime => hairerPsiWickCube N ρ ε ξ q.1 q.2) :=
  ((measurable_hairerPsiField_uncurry N hξ).pow_const 3).sub
    (measurable_const.mul (measurable_hairerPsiField_uncurry N hξ))

/-- **Covariance of the Wick cube of `Ψ`.** `E[:Ψ³:(u) :Ψ³:(v)] = 6 Q_ε(u - v)³`. -/
theorem hairerPsiWickCube_integral_mul (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (u v : SpaceTime) :
    ∫ ω, hairerPsiWickCube N ρ ε ξ ω u * hairerPsiWickCube N ρ ε ξ ω v ∂P =
      6 * hairerCovariance N ρ ε (u - v) ^ 3 := by
  have h := hairerPsiField_isCentredGaussianVector N hρ hε hW hξ ![u, v]
  have h2 := integral_wick_replicate_mul_wick_replicate h 0 1 (k := 3) (l := 3) (by norm_num)
    (by norm_num)
  simp only [List.replicate, wickMonomial_triple_self, ite_true, Matrix.cons_val_zero,
    Matrix.cons_val_one, sub_self] at h2
  simp only [hairerPsiWickCube, hairerWickConstant_eq_covariance_zero]
  convert h2 using 3
  norm_num [Nat.factorial]

/-- The Wick cube of `Ψ` is square integrable. -/
theorem hairerPsiWickCube_memLp (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    MemLp (fun ω => hairerPsiWickCube N ρ ε ξ ω z) 2 P := by
  have h := hairerPsiField_isCentredGaussianVector N hρ hε hW hξ ![z]
  have hi := h.integrable_prod_wickMonomial (L := fun _ : Fin 2 => [0, 0, 0])
  have hm : Measurable fun ω => hairerPsiWickCube N ρ ε ξ ω z :=
    ((measurable_hairerPsiField_apply N hξ z).pow_const 3).sub
      (measurable_const.mul (measurable_hairerPsiField_apply N hξ z))
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Fin.prod_univ_two, sq, wickMonomial_triple_self, hairerPsiWickCube,
    hairerWickConstant_eq_covariance_zero, Matrix.cons_val_zero, sub_self]

end RegularityStructures.Phi43

end
