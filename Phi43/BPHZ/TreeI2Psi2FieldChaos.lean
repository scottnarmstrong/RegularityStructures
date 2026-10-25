/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2FieldFubini
public import Phi43.BPHZ.TreeI2Psi2FieldMean

/-!
# The tree `I(Ψ²) Ψ²`: covariance of kernel-integrated Wick squares, four-argument form

For scales `ε₀, …, ε₃`, noises `ξᵢ`, kernels `g₁, g₃ ∈ L¹`, and points `y, y'`, put
`Yᵢ = :Ψ²_{εᵢ}:` and consider
`E[(∫ g₁ Y₀) Y₁(y) ((∫ g₃ Y₂) Y₃(y'))]`.
By stochastic Fubini and the diagram formula (W3) for `(Y₀(w), Y₁(y), Y₂(w'), Y₃(y'))` it equals
`∫∫ g₁(w) g₃(w') (χ₄ + χ₂ + χ₀)(w, w') dw dw'` with the chaos-`4`, `2`, `0` kernels
`χ₄, χ₂, χ₀` below, whose entries are the cross covariances
`Q_{εᵢ εⱼ}(zᵢ - zⱼ)` for `(z₀, z₁, z₂, z₃) = (w, y, w', y')` [Hai14, (10.39)-(10.42)].
All three pieces are separately integrable.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The chaos-`4` kernel `χ₄(w, w')` of `E[Y₀(w) Y₁(y) Y₂(w') Y₃(y')]`. -/
def hairerI2Psi2Chaos4 (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ ε₁ ε₂ ε₃ : ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickSquareFourChaos4 (hairerCrossCovariance N ρ ε₀ ε₂ (w - w'))
    (hairerCrossCovariance N ρ ε₀ ε₃ (w - y')) (hairerCrossCovariance N ρ ε₁ ε₂ (y - w'))
    (hairerCrossCovariance N ρ ε₁ ε₃ (y - y'))

/-- The chaos-`2` kernel `χ₂(w, w')` of `E[Y₀(w) Y₁(y) Y₂(w') Y₃(y')]`. -/
def hairerI2Psi2Chaos2 (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ ε₁ ε₂ ε₃ : ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickSquareFourChaos2 (hairerCrossCovariance N ρ ε₀ ε₁ (w - y))
    (hairerCrossCovariance N ρ ε₂ ε₃ (w' - y')) (hairerCrossCovariance N ρ ε₀ ε₂ (w - w'))
    (hairerCrossCovariance N ρ ε₀ ε₃ (w - y')) (hairerCrossCovariance N ρ ε₁ ε₂ (y - w'))
    (hairerCrossCovariance N ρ ε₁ ε₃ (y - y'))

/-- The chaos-`0` kernel `χ₀(w, w')` of `E[Y₀(w) Y₁(y) Y₂(w') Y₃(y')]`; it factorises as
`(2 Q_{ε₀ε₁}(w - y)²) (2 Q_{ε₂ε₃}(w' - y')²)`. -/
def hairerI2Psi2Chaos0 (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ ε₁ ε₂ ε₃ : ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickSquareFourChaos0 (hairerCrossCovariance N ρ ε₀ ε₁ (w - y))
    (hairerCrossCovariance N ρ ε₂ ε₃ (w' - y'))

/-- The product `Y₀(w) Y₁(y) Y₂(w') Y₃(y')` of four Wick squares of `Ψ` at scales `ε i` and
noises `ξ i`. -/
def hairerWickSquareFourProduct {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 4 → ℝ)
    (ξ : Fin 4 → Ω → SpaceTime → ℝ) (y y' w w' : SpaceTime) (ω : Ω) : ℝ :=
  hairerPsiWickSquare N ρ (ε 0) (ξ 0) ω w * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y *
    hairerPsiWickSquare N ρ (ε 2) (ξ 2) ω w' * hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y'

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

private theorem abs_mul_four_le' (a b c d : ℝ) :
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

private theorem abs_mul_four_le_pow {a b c d S : ℝ} (ha : |a| ≤ S) (hb : |b| ≤ S) (hc : |c| ≤ S)
    (hd : |d| ≤ S) : |a * b * c * d| ≤ S ^ 4 := by
  have h0 : 0 ≤ S := (abs_nonneg _).trans ha
  rw [abs_mul, abs_mul, abs_mul]
  calc |a| * |b| * |c| * |d| ≤ S * S * S * S := by
        gcongr
    _ = S ^ 4 := by ring

private theorem abs_const_mul_le {k x S : ℝ} (hk : 0 ≤ k) (hx : |x| ≤ S) :
    |k * x| ≤ k * S := by
  rw [abs_mul, abs_of_nonneg hk]
  gcongr

theorem abs_hairerWickSquareFourChaos_le {S c01 c23 c02 c03 c12 c13 : ℝ} (h01 : |c01| ≤ S) (h23 : |c23| ≤ S)
    (h02 : |c02| ≤ S) (h03 : |c03| ≤ S) (h12 : |c12| ≤ S) (h13 : |c13| ≤ S) :
    |hairerWickSquareFourChaos4 c02 c03 c12 c13| ≤ 24 * S ^ 4 ∧
    |hairerWickSquareFourChaos2 c01 c23 c02 c03 c12 c13| ≤ 32 * S ^ 4 ∧
    |hairerWickSquareFourChaos0 c01 c23| ≤ 4 * S ^ 4 := by
  have m1 := abs_const_mul_le (k := 4) (by norm_num) (abs_mul_four_le_pow h02 h02 h13 h13)
  have m2 := abs_const_mul_le (k := 4) (by norm_num) (abs_mul_four_le_pow h03 h03 h12 h12)
  have m3 := abs_const_mul_le (k := 16) (by norm_num) (abs_mul_four_le_pow h02 h03 h12 h13)
  have m4 := abs_const_mul_le (k := 16) (by norm_num) (abs_mul_four_le_pow h01 h23 h02 h13)
  have m5 := abs_const_mul_le (k := 16) (by norm_num) (abs_mul_four_le_pow h01 h23 h03 h12)
  have m6 := abs_const_mul_le (k := 4) (by norm_num) (abs_mul_four_le_pow h01 h01 h23 h23)
  refine ⟨?_, ?_, ?_⟩
  · have e : hairerWickSquareFourChaos4 c02 c03 c12 c13 =
        4 * (c02 * c02 * c13 * c13) + 4 * (c03 * c03 * c12 * c12) +
          16 * (c02 * c03 * c12 * c13) := by
      unfold hairerWickSquareFourChaos4
      ring
    rw [e]
    calc _ ≤ |4 * (c02 * c02 * c13 * c13) + 4 * (c03 * c03 * c12 * c12)| +
          |16 * (c02 * c03 * c12 * c13)| := abs_add_le _ _
      _ ≤ |4 * (c02 * c02 * c13 * c13)| + |4 * (c03 * c03 * c12 * c12)| +
          |16 * (c02 * c03 * c12 * c13)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ 24 * S ^ 4 := by linarith
  · have e : hairerWickSquareFourChaos2 c01 c23 c02 c03 c12 c13 =
        16 * (c01 * c23 * c02 * c13) + 16 * (c01 * c23 * c03 * c12) := by
      unfold hairerWickSquareFourChaos2
      ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)
  · have e : hairerWickSquareFourChaos0 c01 c23 = 4 * (c01 * c01 * c23 * c23) := by
      unfold hairerWickSquareFourChaos0
      ring
    rw [e]
    linarith

variable {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}

/-- The expectation of the four-fold product is the sum of the three chaos kernels. -/
theorem integral_hairerWickSquareFourProduct (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    ∫ ω, hairerWickSquareFourProduct N ρ ε ξ y y' w w' ω ∂P =
      hairerI2Psi2Chaos4 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' w w' +
        hairerI2Psi2Chaos2 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' w w' +
        hairerI2Psi2Chaos0 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' w w' := by
  have h := hairerPsiWickSquare_integral_mul_four N hρ hε hW hξ ![w, y, w', y']
  simpa [hairerWickSquareFourProduct, hairerI2Psi2Chaos4, hairerI2Psi2Chaos2,
    hairerI2Psi2Chaos0] using h

/-- The four-fold product is integrable. -/
theorem integrable_hairerWickSquareFourProduct (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    Integrable (hairerWickSquareFourProduct N ρ ε ξ y y' w w') P := by
  have h := integrable_hairerPsiWickSquare_four N hρ hε hW hξ ![w, y, w', y']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at h
  exact h

/-- The first absolute moment of the four-fold product is bounded uniformly in `(w, w')`. -/
theorem integral_abs_hairerWickSquareFourProduct_le (N : ℕ) (hρ : IsMollifier ρ)
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    ∫ ω, |hairerWickSquareFourProduct N ρ ε ξ y y' w w' ω| ∂P ≤
      15 * (hairerWickConstant N ρ (ε 0) ^ 4 + hairerWickConstant N ρ (ε 1) ^ 4 +
        hairerWickConstant N ρ (ε 2) ^ 4 + hairerWickConstant N ρ (ε 3) ^ 4) := by
  have hprob := hW.isProbabilityMeasure
  have i0 := integrable_hairerPsiWickSquare_pow_four N hρ (hε 0) hW (hξ 0) w
  have i1 := integrable_hairerPsiWickSquare_pow_four N hρ (hε 1) hW (hξ 1) y
  have i2 := integrable_hairerPsiWickSquare_pow_four N hρ (hε 2) hW (hξ 2) w'
  have i3 := integrable_hairerPsiWickSquare_pow_four N hρ (hε 3) hW (hξ 3) y'
  have j01 : Integrable (fun ω => hairerPsiWickSquare N ρ (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4) P := i0.add i1
  have j012 : Integrable (fun ω => hairerPsiWickSquare N ρ (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4 +
      hairerPsiWickSquare N ρ (ε 2) (ξ 2) ω w' ^ 4) P := j01.add i2
  have j0123 : Integrable (fun ω => hairerPsiWickSquare N ρ (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4 +
      hairerPsiWickSquare N ρ (ε 2) (ξ 2) ω w' ^ 4 +
      hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y' ^ 4) P := j012.add i3
  calc _ ≤ ∫ ω, (hairerPsiWickSquare N ρ (ε 0) (ξ 0) ω w ^ 4 +
        hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y ^ 4 + hairerPsiWickSquare N ρ (ε 2) (ξ 2) ω w' ^ 4 +
        hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y' ^ 4) / 4 ∂P :=
        integral_mono (integrable_hairerWickSquareFourProduct N hρ hε hW hξ y y' w w').abs
          (j0123.div_const 4) fun ω => abs_mul_four_le' _ _ _ _
    _ = _ := by
        rw [integral_div, integral_add j012 i3, integral_add j01 i2, integral_add i0 i1,
          integral_hairerPsiWickSquare_pow_four N hρ (hε 0) hW (hξ 0) w,
          integral_hairerPsiWickSquare_pow_four N hρ (hε 1) hW (hξ 1) y,
          integral_hairerPsiWickSquare_pow_four N hρ (hε 2) hW (hξ 2) w',
          integral_hairerPsiWickSquare_pow_four N hρ (hε 3) hW (hξ 3) y']
        ring

end RegularityStructures.Phi43

end
