/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeWickDifferenceCov
public import Phi43.BPHZ.TreeWickSquareFour
public import Phi43.BPHZ.TreeWickCube
public import RegularityStructures.BPHZ.GaussianWickBlocksFour
public import Phi43.BPHZ.TreeWickSquare

/-!
# The tree `I(Ψ³) Ψ²`: the diagram formula for `:Ψ³: :Ψ²: :Ψ³: :Ψ²:` at four scales

For scales `ε₀, …, ε₃`, noises `ξ₀, …, ξ₃` and points `z₀, …, z₃`, the vector
`(Ψ_{εᵢ}(zᵢ))ᵢ` is a centred Gaussian vector with covariance `c_{ij} = Q_{εᵢ εⱼ}(zᵢ - zⱼ)`, and
the diagram formula (W4) gives
`E[:Ψ³:(z₀) :Ψ²:(z₁) :Ψ³:(z₂) :Ψ²:(z₃)] = χ₅ + χ₃ + χ₁`, sorted by the number `k` of covariance
entries linking `{0, 1}` with `{2, 3}` (the chaos of the field):

* `χ₅ = 12 c₀₂³ c₁₃² + 72 c₀₂² c₀₃ c₁₂ c₁₃ + 36 c₀₂ c₀₃² c₁₂²`,
* `χ₃ = 72 c₀₁ c₀₂² c₁₃ c₂₃ + 144 c₀₁ c₀₂ c₀₃ c₁₂ c₂₃`,
* `χ₁ = 36 c₀₁² c₀₂ c₂₃²`.

We also record integrability of the product.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The chaos-`5` part of `E[:X₀³: :X₁²: :X₂³: :X₃²:]`, in terms of `c02, c03, c12, c13`. -/
def hairerWickCubeSquareChaos5 (c02 c03 c12 c13 : ℝ) : ℝ :=
  12 * c02 ^ 3 * c13 ^ 2 + 72 * c02 ^ 2 * c03 * c12 * c13 + 36 * c02 * c03 ^ 2 * c12 ^ 2

/-- The chaos-`3` part of `E[:X₀³: :X₁²: :X₂³: :X₃²:]`, in terms of
`c01, c23, c02, c03, c12, c13`. -/
def hairerWickCubeSquareChaos3 (c01 c23 c02 c03 c12 c13 : ℝ) : ℝ :=
  72 * c01 * c02 ^ 2 * c13 * c23 + 144 * c01 * c02 * c03 * c12 * c23

/-- The chaos-`1` part of `E[:X₀³: :X₁²: :X₂³: :X₃²:]`, in terms of `c01, c23, c02`. -/
def hairerWickCubeSquareChaos1 (c01 c23 c02 : ℝ) : ℝ :=
  36 * c01 ^ 2 * c02 * c23 ^ 2

/-- The chaos-`5` kernel `χ₅(w, w')` of `E[Y₀(w) Y₁(y) Y₂(w') Y₃(y')]`
(`Y₀, Y₂` Wick cubes, `Y₁, Y₃` Wick squares); entries `Q_{εᵢ εⱼ}(zᵢ - zⱼ)` at
`(z₀, z₁, z₂, z₃) = (w, y, w', y')`. -/
def hairerI3Psi2Chaos5 (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ ε₁ ε₂ ε₃ : ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickCubeSquareChaos5 (hairerCrossCovariance N ρ ε₀ ε₂ (w - w'))
    (hairerCrossCovariance N ρ ε₀ ε₃ (w - y')) (hairerCrossCovariance N ρ ε₁ ε₂ (y - w'))
    (hairerCrossCovariance N ρ ε₁ ε₃ (y - y'))

/-- The chaos-`3` kernel `χ₃(w, w')` of `E[Y₀(w) Y₁(y) Y₂(w') Y₃(y')]`. -/
def hairerI3Psi2Chaos3 (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ ε₁ ε₂ ε₃ : ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickCubeSquareChaos3 (hairerCrossCovariance N ρ ε₀ ε₁ (w - y))
    (hairerCrossCovariance N ρ ε₂ ε₃ (w' - y')) (hairerCrossCovariance N ρ ε₀ ε₂ (w - w'))
    (hairerCrossCovariance N ρ ε₀ ε₃ (w - y')) (hairerCrossCovariance N ρ ε₁ ε₂ (y - w'))
    (hairerCrossCovariance N ρ ε₁ ε₃ (y - y'))

/-- The chaos-`1` kernel `χ₁(w, w')` of `E[Y₀(w) Y₁(y) Y₂(w') Y₃(y')]`. -/
def hairerI3Psi2Chaos1 (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ ε₁ ε₂ ε₃ : ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickCubeSquareChaos1 (hairerCrossCovariance N ρ ε₀ ε₁ (w - y))
    (hairerCrossCovariance N ρ ε₂ ε₃ (w' - y')) (hairerCrossCovariance N ρ ε₀ ε₂ (w - w'))

/-- The product `Y₀(w) Y₁(y) Y₂(w') Y₃(y')` of two Wick cubes at `w, w'` (scales `ε 0`, `ε 2`) and
two Wick squares at `y, y'` (scales `ε 1`, `ε 3`). -/
def hairerWickCubeSquareFourProduct {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (ε : Fin 4 → ℝ) (ξ : Fin 4 → Ω → SpaceTime → ℝ) (y y' w w' : SpaceTime) (ω : Ω) : ℝ :=
  hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y *
    hairerPsiWickCube N ρ (ε 2) (ξ 2) ω w' * hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y'

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}

omit [MeasurableSpace Ω] in
/-- The product of two Wick cubes and two Wick squares at four scales is the product of Wick
monomials of the multiscale vector. -/
theorem hairerWickCubeSquareFourProduct_eq_wickMonomial (N : ℕ) (z : Fin 4 → SpaceTime)
    (ω : Ω) :
    hairerPsiWickCube N ρ (ε 0) (ξ 0) ω (z 0) * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) *
        hairerPsiWickCube N ρ (ε 2) (ξ 2) ω (z 2) * hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω (z 3) =
      wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 3 0) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 2 1) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 3 2) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 2 3) (fun j => hairerPsiField N (ξ j) ω (z j)) := by
  have c0 := hairerPsiWickCube_eq_wickMonomial_multiscale (ρ := ρ) N ε ξ z ω 0
  have c2 := hairerPsiWickCube_eq_wickMonomial_multiscale (ρ := ρ) N ε ξ z ω 2
  have s1 := hairerPsiWickSquare_eq_wickMonomial_multiscale (ρ := ρ) N ε ξ z ω 1
  have s3 := hairerPsiWickSquare_eq_wickMonomial_multiscale (ρ := ρ) N ε ξ z ω 3
  rw [c0, c2, s1, s3]
  rfl

/-- **Four Wick monomials at several scales** (W4 for the tree `Ψ`).
`E[:Ψ³_{ε₀}:(z₀) :Ψ²_{ε₁}:(z₁) :Ψ³_{ε₂}:(z₂) :Ψ²_{ε₃}:(z₃)] = χ₅ + χ₃ + χ₁` with covariance
entries `c_{ij} = Q_{εᵢ εⱼ}(zᵢ - zⱼ)`. -/
theorem hairerPsiWickCubeSquare_integral_mul_four (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (z : Fin 4 → SpaceTime) :
    ∫ ω, hairerPsiWickCube N ρ (ε 0) (ξ 0) ω (z 0) * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) *
        hairerPsiWickCube N ρ (ε 2) (ξ 2) ω (z 2) *
        hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω (z 3) ∂P =
      hairerWickCubeSquareChaos5 (hairerCrossCovariance N ρ (ε 0) (ε 2) (z 0 - z 2))
          (hairerCrossCovariance N ρ (ε 0) (ε 3) (z 0 - z 3))
          (hairerCrossCovariance N ρ (ε 1) (ε 2) (z 1 - z 2))
          (hairerCrossCovariance N ρ (ε 1) (ε 3) (z 1 - z 3)) +
        hairerWickCubeSquareChaos3 (hairerCrossCovariance N ρ (ε 0) (ε 1) (z 0 - z 1))
          (hairerCrossCovariance N ρ (ε 2) (ε 3) (z 2 - z 3))
          (hairerCrossCovariance N ρ (ε 0) (ε 2) (z 0 - z 2))
          (hairerCrossCovariance N ρ (ε 0) (ε 3) (z 0 - z 3))
          (hairerCrossCovariance N ρ (ε 1) (ε 2) (z 1 - z 2))
          (hairerCrossCovariance N ρ (ε 1) (ε 3) (z 1 - z 3)) +
        hairerWickCubeSquareChaos1 (hairerCrossCovariance N ρ (ε 0) (ε 1) (z 0 - z 1))
          (hairerCrossCovariance N ρ (ε 2) (ε 3) (z 2 - z 3))
          (hairerCrossCovariance N ρ (ε 0) (ε 2) (z 0 - z 2)) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscale N hρ hε hW hξ z
  have hw := integral_wick_three_mul_wick_two_mul_wick_three_mul_wick_two h 0 1 2 3
  simp_rw [hairerWickCubeSquareFourProduct_eq_wickMonomial N z]
  rw [hw]
  unfold hairerWickCubeSquareChaos5 hairerWickCubeSquareChaos3 hairerWickCubeSquareChaos1
  ring

/-- The product of two Wick cubes and two Wick squares at several scales is integrable. -/
theorem integrable_hairerPsiWickCubeSquare_four (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (z : Fin 4 → SpaceTime) :
    Integrable (fun ω => hairerPsiWickCube N ρ (ε 0) (ξ 0) ω (z 0) *
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) * hairerPsiWickCube N ρ (ε 2) (ξ 2) ω (z 2) *
      hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω (z 3)) P := by
  have h := hairerPsiField_isCentredGaussianVector_multiscale N hρ hε hW hξ z
  have hi := h.integrable_prod_wickMonomial (L := ![List.replicate 3 0, List.replicate 2 1,
    List.replicate 3 2, List.replicate 2 3])
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at hi
  exact hi.congr (Filter.Eventually.of_forall fun ω =>
    (hairerWickCubeSquareFourProduct_eq_wickMonomial N z ω).symm)

/-- The expectation of the four-fold product is the sum of the three chaos kernels. -/
theorem integral_hairerWickCubeSquareFourProduct (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    ∫ ω, hairerWickCubeSquareFourProduct N ρ ε ξ y y' w w' ω ∂P =
      hairerI3Psi2Chaos5 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' w w' +
        hairerI3Psi2Chaos3 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' w w' +
        hairerI3Psi2Chaos1 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' w w' := by
  have h := hairerPsiWickCubeSquare_integral_mul_four N hρ hε hW hξ ![w, y, w', y']
  simpa [hairerWickCubeSquareFourProduct, hairerI3Psi2Chaos5, hairerI3Psi2Chaos3,
    hairerI3Psi2Chaos1] using h

/-- The four-fold product is integrable. -/
theorem integrable_hairerWickCubeSquareFourProduct (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    Integrable (hairerWickCubeSquareFourProduct N ρ ε ξ y y' w w') P := by
  have h := integrable_hairerPsiWickCubeSquare_four N hρ hε hW hξ ![w, y, w', y']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at h
  exact h

end RegularityStructures.Phi43

end
