/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Translate

/-!
# The polynomial regularity structure `T̄_N`

The structure group `polyGroup N` is the group of translations `Γ_h : X^k ↦ (X + h)^k`, `h ∈ ℝ⁴`,
and `polynomialStructure N` is the regularity structure with basis `X^k`, `|k|_𝔰 < N`, degrees
`|k|_𝔰` and this group [Hai14, Section 2.2, Remark 2.23, (2.20)-(2.21)].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {N : ℕ}

/-- The translation `Γ_h` as an element of `GL(PolyIndex N → ℝ)`, with inverse `Γ_{-h}`. -/
def polyUnit (h : Fin 4 → ℝ) : LinearMap.GeneralLinearGroup ℝ (PolyIndex N → ℝ) where
  val := polyTranslate h
  inv := polyTranslate (-h)
  val_inv := by
    rw [Module.End.mul_eq_comp, polyTranslate_add, add_neg_cancel, polyTranslate_zero]; rfl
  inv_val := by
    rw [Module.End.mul_eq_comp, polyTranslate_add, neg_add_cancel, polyTranslate_zero]; rfl

/-- The group homomorphism `h ↦ Γ_h` from `(ℝ⁴, +)` to `GL(PolyIndex N → ℝ)`. -/
def polyHom (N : ℕ) : Multiplicative (Fin 4 → ℝ) →* LinearMap.GeneralLinearGroup ℝ (PolyIndex N → ℝ)
    where
  toFun h := polyUnit (Multiplicative.toAdd h)
  map_one' := Units.ext polyTranslate_zero
  map_mul' a b := Units.ext (by
    rw [Units.val_mul, Module.End.mul_eq_comp]
    exact (polyTranslate_add _ _).symm)

/-- The structure group of translations. -/
def polyGroup (N : ℕ) : Subgroup (LinearMap.GeneralLinearGroup ℝ (PolyIndex N → ℝ)) :=
  (polyHom N).range

/-- The polynomial regularity structure `T̄_N` [Hai14, Remark 2.23]. -/
def polynomialStructure (N : ℕ) : RegularityStructure (PolyIndex N) where
  deg := polyDeg N
  group := polyGroup N
  isGradedUnipotent := by
    rintro g ⟨h, rfl⟩
    exact isGradedUnipotent_polyTranslate _

/-- The polynomial model `Π_x τ (z) = (z - x)^τ` at the level of functions. -/
def polyEval (x : ParabolicSpace) (τ : PolyIndex N → ℝ) (z : ParabolicSpace) : ℝ :=
  MvPolynomial.eval (parabolicCoords (z - x)) (toPoly N τ)

end RegularityStructures

end

public section

namespace RegularityStructures

variable {N : ℕ}

theorem parabolicCoords_add (a b : ParabolicSpace) :
    parabolicCoords (a + b) = parabolicCoords a + parabolicCoords b := by
  funext i
  fin_cases i <;> simp [parabolicCoords]

theorem eval_translateAlg (g c : Fin 4 → ℝ) (p : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial.eval g (translateAlg c p) = MvPolynomial.eval (g + c) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp]; simp [translateAlg]

/-- `Π_x Γ_{xy} = Π_y` with `Γ_{xy} = Γ_{x - y}`. -/
theorem polyEval_polyTranslate (x y : ParabolicSpace) (τ : PolyIndex N → ℝ) (z : ParabolicSpace) :
    polyEval x (polyTranslate (parabolicCoords (x - y)) τ) z = polyEval y τ z := by
  unfold polyEval
  rw [toPoly_polyTranslate, eval_translateAlg, ← parabolicCoords_add]
  have : z - x + (x - y) = z - y := by abel
  rw [this]

theorem polyEval_single (x : ParabolicSpace) (k : PolyIndex N) (z : ParabolicSpace) :
    polyEval x (Pi.single k 1) z = evalParabolic (MvPolynomial.monomial k.1 1) (z - x) := by
  simp [polyEval, evalParabolic, toPoly_single]

end RegularityStructures

end
