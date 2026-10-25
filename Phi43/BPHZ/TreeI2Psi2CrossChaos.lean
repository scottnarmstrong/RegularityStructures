/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2FieldChaos
public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoWick

/-!
# The tree `I(Ψ²) Ψ²`: four Wick squares at several mollifiers

Generalisation of `TreeI2Psi2FieldChaos` and `TreeI2Psi2FieldChaosFour` to a family of four noises
built from possibly different mollifiers `ρ i` and scales `ε i` of the same white noise.  The
chaos kernels `χ₄, χ₂, χ₀` have the entries `Q_{(ρ i, ε i),(ρ j, ε j)}(zᵢ - zⱼ)` (the covariance of
the Gaussian vector of `hairerPsiField_isCentredGaussianVector_multiscaleTwo`), and the expectation
of the four-fold product of Wick squares is `χ₄ + χ₂ + χ₀`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The chaos-`4` kernel `χ₄(w, w')` of `E[Y₀(w) Y₁(y) Y₂(w') Y₃(y')]` with mixed mollifiers. -/
def hairerI2Psi2Chaos4Two (N : ℕ) (ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 4 → ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickSquareFourChaos4 (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (w - w'))
    (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (w - y'))
    (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (y - w'))
    (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (y - y'))

/-- The chaos-`2` kernel `χ₂(w, w')` with mixed mollifiers. -/
def hairerI2Psi2Chaos2Two (N : ℕ) (ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 4 → ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickSquareFourChaos2 (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (w - y))
    (hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (w' - y'))
    (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (w - w'))
    (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (w - y'))
    (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (y - w'))
    (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (y - y'))

/-- The chaos-`0` kernel `χ₀(w, w')` with mixed mollifiers. -/
def hairerI2Psi2Chaos0Two (N : ℕ) (ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 4 → ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickSquareFourChaos0 (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (w - y))
    (hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (w' - y'))

/-- The product `Y₀(w) Y₁(y) Y₂(w') Y₃(y')` of four Wick squares at mixed mollifiers. -/
def hairerWickSquareFourProductTwo {Ω : Type*} (N : ℕ) (ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ)
    (ε : Fin 4 → ℝ) (ξ : Fin 4 → Ω → SpaceTime → ℝ) (y y' w w' : SpaceTime) (ω : Ω) : ℝ :=
  hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω w * hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y *
    hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω w' * hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y'

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}

private theorem abs_mul_four_le_two (a b c d : ℝ) :
    |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  have h1 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have h2 : |c * d| ≤ (c ^ 2 + d ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|c| - |d|), sq_abs c, sq_abs d]
  have h3 : |a * b * c * d| ≤ (a ^ 2 + b ^ 2) / 2 * ((c ^ 2 + d ^ 2) / 2) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith [sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (b ^ 2 - d ^ 2)]

/-- **Four Wick squares at several mollifiers** (the formula (W3) of
`RegularityStructures.BPHZ.GaussianWickBlocksFour` for the tree `Ψ`). -/
theorem hairerPsiWickSquare_integral_mul_four_two (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (z : Fin 4 → SpaceTime) :
    ∫ ω, hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω (z 0) *
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) *
        hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω (z 2) *
        hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω (z 3) ∂P =
      hairerWickSquareFourChaos4
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (z 0 - z 2))
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (z 0 - z 3))
          (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (z 1 - z 2))
          (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (z 1 - z 3)) +
        hairerWickSquareFourChaos2
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (z 0 - z 1))
          (hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (z 2 - z 3))
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (z 0 - z 2))
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (z 0 - z 3))
          (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (z 1 - z 2))
          (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (z 1 - z 3)) +
        hairerWickSquareFourChaos0
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (z 0 - z 1))
          (hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (z 2 - z 3)) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N hρ hε hW hξ z
  have hw := integral_wick_two_mul_wick_two_mul_wick_two_mul_wick_two h 0 1 2 3
  have e : ∀ ω (i : Fin 4), hairerPsiWickSquare N (ρ i) (ε i) (ξ i) ω (z i) =
      wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
        (List.replicate 2 i) (fun j => hairerPsiField N (ξ j) ω (z j)) := fun ω i =>
    hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω i
  have hcongr : ∫ ω, hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω (z 0) *
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) *
        hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω (z 2) *
        hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω (z 3) ∂P = ∫ ω,
      wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 2 0) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 2 1) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 2 2) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 2 3) (fun j => hairerPsiField N (ξ j) ω (z j)) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [e ω 0, e ω 1, e ω 2, e ω 3]
  rw [hcongr, hw]
  unfold hairerWickSquareFourChaos4 hairerWickSquareFourChaos2 hairerWickSquareFourChaos0
  ring

/-- The product of four Wick squares at several mollifiers is integrable. -/
theorem integrable_hairerPsiWickSquare_four_two (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (z : Fin 4 → SpaceTime) :
    Integrable (fun ω => hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω (z 0) *
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) *
      hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω (z 2) *
      hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω (z 3)) P := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N hρ hε hW hξ z
  have hi := h.integrable_prod_wickMonomial (L := fun j : Fin 4 => List.replicate 2 j)
  simp only [Fin.prod_univ_four] at hi
  refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 0,
    hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 1,
    hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 2,
    hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 3]
  rfl

/-- The expectation of the four-fold product is the sum of the three chaos kernels. -/
theorem integral_hairerWickSquareFourProductTwo (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    ∫ ω, hairerWickSquareFourProductTwo N ρ ε ξ y y' w w' ω ∂P =
      hairerI2Psi2Chaos4Two N ρ ε y y' w w' + hairerI2Psi2Chaos2Two N ρ ε y y' w w' +
        hairerI2Psi2Chaos0Two N ρ ε y y' w w' := by
  have h := hairerPsiWickSquare_integral_mul_four_two N hρ hε hW hξ ![w, y, w', y']
  simpa [hairerWickSquareFourProductTwo, hairerI2Psi2Chaos4Two, hairerI2Psi2Chaos2Two,
    hairerI2Psi2Chaos0Two] using h

/-- The four-fold product is integrable. -/
theorem integrable_hairerWickSquareFourProductTwo (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    Integrable (hairerWickSquareFourProductTwo N ρ ε ξ y y' w w') P := by
  have h := integrable_hairerPsiWickSquare_four_two N hρ hε hW hξ ![w, y, w', y']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at h
  exact h

/-- The first absolute moment of the four-fold product is bounded uniformly in `(w, w')`. -/
theorem integral_abs_hairerWickSquareFourProductTwo_le (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    ∫ ω, |hairerWickSquareFourProductTwo N ρ ε ξ y y' w w' ω| ∂P ≤
      15 * (hairerWickConstant N (ρ 0) (ε 0) ^ 4 + hairerWickConstant N (ρ 1) (ε 1) ^ 4 +
        hairerWickConstant N (ρ 2) (ε 2) ^ 4 + hairerWickConstant N (ρ 3) (ε 3) ^ 4) := by
  have hprob := hW.isProbabilityMeasure
  have i0 := integrable_hairerPsiWickSquare_pow_four N (hρ 0) (hε 0) hW (hξ 0) w
  have i1 := integrable_hairerPsiWickSquare_pow_four N (hρ 1) (hε 1) hW (hξ 1) y
  have i2 := integrable_hairerPsiWickSquare_pow_four N (hρ 2) (hε 2) hW (hξ 2) w'
  have i3 := integrable_hairerPsiWickSquare_pow_four N (hρ 3) (hε 3) hW (hξ 3) y'
  have j01 : Integrable (fun ω => hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4) P := i0.add i1
  have j012 : Integrable (fun ω => hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4 +
      hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω w' ^ 4) P := j01.add i2
  have j0123 : Integrable (fun ω => hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4 +
      hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω w' ^ 4 +
      hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y' ^ 4) P := j012.add i3
  calc _ ≤ ∫ ω, (hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4 +
        hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω w' ^ 4 +
        hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y' ^ 4) / 4 ∂P :=
        integral_mono (integrable_hairerWickSquareFourProductTwo N hρ hε hW hξ y y' w w').abs
          (j0123.div_const 4) fun ω => abs_mul_four_le_two _ _ _ _
    _ = _ := by
        rw [integral_div, integral_add j012 i3, integral_add j01 i2, integral_add i0 i1,
          integral_hairerPsiWickSquare_pow_four N (hρ 0) (hε 0) hW (hξ 0) w,
          integral_hairerPsiWickSquare_pow_four N (hρ 1) (hε 1) hW (hξ 1) y,
          integral_hairerPsiWickSquare_pow_four N (hρ 2) (hε 2) hW (hξ 2) w',
          integral_hairerPsiWickSquare_pow_four N (hρ 3) (hε 3) hW (hξ 3) y']
        ring

end RegularityStructures.Phi43

end
