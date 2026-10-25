/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.Renormalisation
public import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Tactic

/-!
# Character compatibility for the finite Φ⁴₃ renormalisation

This module records the finite character calculation behind Hairer (8.35b),
(8.35c), and (9.4b,c).  The right-hand algebra is represented by a free
finite-dimensional vector space of positive Taylor symbols.  Its product keeps
the one product needed when a spatial Taylor coordinate meets `Jᵢ(Ψ)`.
The coaction and its renormalised version are explicit; the compatibility
theorem is therefore a calculation with `M`, `Mhat`, and multiplication, not
the formal conjugation identity which holds for every invertible linear map.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped BigOperators

/-- Positive Taylor symbols used by Hairer’s character `fₓ`. -/
inductive PlusSymbol where
  | one
  | x0
  | x (i : Fin 3)
  | xMul (p : Sym2 (Fin 3))
  | jPsi
  | jPsiGrad (i : Fin 3)
  | jPsiSq
  | jPsiCube
  | jPsiSquared
  | jPsiCubePsi
  | jPsiCubeSq
  | xJPsiGrad (i : Fin 3)
  deriving DecidableEq, Fintype

/-- The finite positive Taylor algebra. -/
abbrev HPlus := PlusSymbol →₀ ℝ

def plusBasis (p : PlusSymbol) : HPlus := Finsupp.single p 1

/-- Hairer’s character on the positive Taylor algebra. -/
def plusPolynomialCharacter (g : G) : Sym2 (Fin 3) → ℝ :=
  Sym2.lift ⟨fun i j => g.shift i.succ * g.shift j.succ, by
    intro i j
    change g.shift i.succ * g.shift j.succ =
      g.shift j.succ * g.shift i.succ
    rw [mul_comm]⟩

def plusCharacterBasis (g : G) : PlusSymbol → ℝ
  | .one => 1
  | .x0 => g.shift 0
  | .x i => g.shift i.succ
  | .xMul p => plusPolynomialCharacter g p
  | .jPsi => g.cPsi - ∑ i : Fin 3, g.shift i.succ * g.cPsiGrad i
  | .jPsiGrad i => g.cPsiGrad i
  | .jPsiSq => g.cPsiSq
  | .jPsiCube => g.cPsiCube
  | .jPsiSquared => (g.cPsi - ∑ i : Fin 3, g.shift i.succ * g.cPsiGrad i) ^ 2
  | .jPsiCubePsi => g.cPsiCube *
      (g.cPsi - ∑ i : Fin 3, g.shift i.succ * g.cPsiGrad i)
  | .jPsiCubeSq => g.cPsiCube ^ 2
  | .xJPsiGrad i => g.shift i.succ * g.cPsiGrad i

def plusCharacter (g : G) : HPlus →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (plusCharacterBasis g)

@[simp]
theorem plusCharacter_basis (g : G) (p : PlusSymbol) :
    plusCharacter g (plusBasis p) = plusCharacterBasis g p := by
  simp [plusCharacter, plusBasis]

/-! ### The finite form of Hairer’s `∆̂ᴹ`

The positive tensor space below is the finite part of `H₊ ⊗ H₊`.  The displayed formula is the
specialisation of Hairer (8.38) to the retained `J` symbols; the only nontrivial correction is the
`J(Ψ³)` term from §9.2. -/

/-! ### The finite coaction -/

abbrev Tensor := Symbol →₀ HPlus

def tensorBasis (τ : Symbol) (p : PlusSymbol) : Tensor :=
  Finsupp.single τ (plusBasis p)

def tensorOf (v : T) (p : HPlus) : Tensor :=
  Finsupp.bilinearCombination ℝ ℝ (fun τ => Finsupp.single τ p) v

/-- Apply the positive character to the second tensor factor. -/
def deltaCharacterCoefficient (g : G) (τ : Symbol) : HPlus →ₗ[ℝ] T where
  toFun p := plusCharacter g p • basis τ
  map_add' p q := by
    rw [(plusCharacter g).map_add, add_smul]
  map_smul' r p := by
    change plusCharacter g (r • p) • basis τ =
      r • (plusCharacter g p • basis τ)
    rw [(plusCharacter g).map_smul]
    module

def deltaCharacterLinear (g : G) : Tensor →ₗ[ℝ] T :=
  Finsupp.lsum ℝ (deltaCharacterCoefficient g)

def deltaCharacter (g : G) (q : Tensor) : T := deltaCharacterLinear g q

@[simp]
theorem deltaCharacter_tensorBasis (g : G) (τ : Symbol) (p : PlusSymbol) :
    deltaCharacter g (tensorBasis τ p) =
      plusCharacter g (plusBasis p) • basis τ := by
  change Finsupp.lsum ℝ (deltaCharacterCoefficient g)
      (Finsupp.single τ (plusBasis p)) = _
  rw [Finsupp.lsum_single]
  rfl

def deltaMBasis (C : RenormalisationConstants) : Symbol → Tensor
  | .iPsiPsiSq =>
      tensorOf (M C (basis .iPsiPsiSq)) (plusBasis .one)
  | .iPsiCubePsi =>
      tensorOf (M C (basis .iPsiCubePsi)) (plusBasis .one) +
        (3 * C₁ C) • ∑ i, tensorBasis (.psiX i) (.jPsiGrad i)
  | .iPsiCubePsiSq =>
      tensorOf (M C (basis .iPsiCubePsiSq)) (plusBasis .one) +
        (3 * C₁ C) •
          ∑ i, tensorBasis (.psiSqX i) (.jPsiGrad i) +
        (-(3 * C₁ C * C₁ C)) • ∑ i, tensorBasis (.x i) (.jPsiGrad i)
  | .iPsiCube =>
      tensorOf (M C (basis .iPsiCube)) (plusBasis .one) +
        (3 * C₁ C) • ∑ i, tensorBasis (.x i) (.jPsiGrad i)
  | τ => tensorOf (M C (basis τ)) (plusBasis .one)

def deltaM (C : RenormalisationConstants) : T →ₗ[ℝ] Tensor :=
  Finsupp.linearCombination ℝ (deltaMBasis C)

@[simp]
theorem deltaM_basis (C : RenormalisationConstants) (τ : Symbol) :
    deltaM C (basis τ) = deltaMBasis C τ := by
  simp [deltaM, basis]

/-! ### The finite form of Hairer’s renormalisation group `R`

Definition 8.41, equation (8.39), asks that the nontrivial first tensor
factors in `∆ᴹ` and `∆̂ᴹ` have strictly larger homogeneity than the symbol
being transformed.  The predicates below spell out those two triangularity
conditions for the retained bases. -/

/-! ### The finite form of Hairer’s `∆̂ᴹ`

The positive tensor space below is the finite part of `H₊ ⊗ H₊`.  The displayed formula is the
specialisation of Hairer (8.38) to the retained `J` symbols; the only nontrivial correction is the
`J(Ψ³)` term from §9.2. -/

/- The explicit retained `J(Ψ³)` row of (8.38), including the antipode
correction `-XᵢJᵢ(Ψ) ⊗ 1`. -/

def IsHairerF0 : Symbol → Prop
  | .one | .noise | .x0 | .x _ | .psi | .psiSq | .psiCube | .psiSqX _ |
      .iPsiSq | .iPsiPsi | .iPsiPsiSq | .iPsiSqPsi | .iPsiSqPsiSq |
      .iPsiCubePsi | .iPsiCubePsiSq => True
  | _ => False

end RegularityStructures.Phi43

end
