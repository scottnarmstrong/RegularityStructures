/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeWickDifferenceCov
public import RegularityStructures.BPHZ.GaussianWickBlocksFour
public import Phi43.BPHZ.TreeWickSquare

/-!
# Four Wick squares of the tree `Ψ` at several scales

For scales `ε₁, …, ε₄`, noises `ξ₁, …, ξ₄` and points `z₁, …, z₄`, the vector
`(Ψ_{εᵢ}(zᵢ))ᵢ` is a centred Gaussian vector with covariance `c_{ij} = Q_{εᵢ εⱼ}(zᵢ - zⱼ)`, and
the diagram formula (W3) gives
`E[:Ψ²:(z₁) :Ψ²:(z₂) :Ψ²:(z₃) :Ψ²:(z₄)] = χ₄ + χ₂ + χ₀`, where, with `c_{ij}` for `i < j`,

* `χ₄ = 4 c₁₃² c₂₄² + 4 c₁₄² c₂₃² + 16 c₁₃ c₁₄ c₂₃ c₂₄` (no contraction between `(1,3)` and
  `(2,4)` block pairs: chaos `4`),
* `χ₂ = 16 c₁₂ c₃₄ (c₁₃ c₂₄ + c₁₄ c₂₃)` (one contraction in each factor: chaos `2`),
* `χ₀ = 4 c₁₂² c₃₄²` (two contractions in each factor: chaos `0`).

The indices below are `0, 1, 2, 3`.  We also record integrability of the product and the
fourth moment `E[:Ψ²:(z)⁴] = 60 Q_ε(0)⁴`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The chaos-`4` part of `E[:X₀²: :X₁²: :X₂²: :X₃²:]`, in terms of the covariance entries
`c02, c03, c12, c13`. -/
def hairerWickSquareFourChaos4 (c02 c03 c12 c13 : ℝ) : ℝ :=
  4 * c02 ^ 2 * c13 ^ 2 + 4 * c03 ^ 2 * c12 ^ 2 + 16 * (c02 * c03 * c12 * c13)

/-- The chaos-`2` part of `E[:X₀²: :X₁²: :X₂²: :X₃²:]`, in terms of the covariance entries
`c01, c23, c02, c03, c12, c13`. -/
def hairerWickSquareFourChaos2 (c01 c23 c02 c03 c12 c13 : ℝ) : ℝ :=
  16 * c01 * c23 * (c02 * c13 + c03 * c12)

/-- The chaos-`0` part of `E[:X₀²: :X₁²: :X₂²: :X₃²:]`, in terms of `c01, c23`. -/
def hairerWickSquareFourChaos0 (c01 c23 : ℝ) : ℝ :=
  4 * c01 ^ 2 * c23 ^ 2

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- **Four Wick squares at several scales** (W3 for the tree `Ψ`).
`E[:Ψ²_{ε₀}:(z₀) :Ψ²_{ε₁}:(z₁) :Ψ²_{ε₂}:(z₂) :Ψ²_{ε₃}:(z₃)] = χ₄ + χ₂ + χ₀` with covariance
entries `c_{ij} = Q_{εᵢ εⱼ}(zᵢ - zⱼ)`. -/
theorem hairerPsiWickSquare_integral_mul_four (N : ℕ) (hρ : IsMollifier ρ) {ε : Fin 4 → ℝ}
    {ξ : Fin 4 → Ω → SpaceTime → ℝ} (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (z : Fin 4 → SpaceTime) :
    ∫ ω, hairerPsiWickSquare N ρ (ε 0) (ξ 0) ω (z 0) * hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) *
        hairerPsiWickSquare N ρ (ε 2) (ξ 2) ω (z 2) *
        hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω (z 3) ∂P =
      hairerWickSquareFourChaos4 (hairerCrossCovariance N ρ (ε 0) (ε 2) (z 0 - z 2))
          (hairerCrossCovariance N ρ (ε 0) (ε 3) (z 0 - z 3))
          (hairerCrossCovariance N ρ (ε 1) (ε 2) (z 1 - z 2))
          (hairerCrossCovariance N ρ (ε 1) (ε 3) (z 1 - z 3)) +
        hairerWickSquareFourChaos2 (hairerCrossCovariance N ρ (ε 0) (ε 1) (z 0 - z 1))
          (hairerCrossCovariance N ρ (ε 2) (ε 3) (z 2 - z 3))
          (hairerCrossCovariance N ρ (ε 0) (ε 2) (z 0 - z 2))
          (hairerCrossCovariance N ρ (ε 0) (ε 3) (z 0 - z 3))
          (hairerCrossCovariance N ρ (ε 1) (ε 2) (z 1 - z 2))
          (hairerCrossCovariance N ρ (ε 1) (ε 3) (z 1 - z 3)) +
        hairerWickSquareFourChaos0 (hairerCrossCovariance N ρ (ε 0) (ε 1) (z 0 - z 1))
          (hairerCrossCovariance N ρ (ε 2) (ε 3) (z 2 - z 3)) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscale N hρ hε hW hξ z
  have hw := integral_wick_two_mul_wick_two_mul_wick_two_mul_wick_two h 0 1 2 3
  have e : ∀ ω (i : Fin 4), hairerPsiWickSquare N ρ (ε i) (ξ i) ω (z i) =
      wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
        (List.replicate 2 i) (fun j => hairerPsiField N (ξ j) ω (z j)) := fun ω i =>
    hairerPsiWickSquare_eq_wickMonomial_multiscale N ε ξ z ω i
  have hcongr : ∫ ω, hairerPsiWickSquare N ρ (ε 0) (ξ 0) ω (z 0) *
        hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) * hairerPsiWickSquare N ρ (ε 2) (ξ 2) ω (z 2) *
        hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω (z 3) ∂P = ∫ ω,
      wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 2 0) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 2 1) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 2 2) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b))
          (List.replicate 2 3) (fun j => hairerPsiField N (ξ j) ω (z j)) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [e ω 0, e ω 1, e ω 2, e ω 3]
  rw [hcongr, hw]
  unfold hairerWickSquareFourChaos4 hairerWickSquareFourChaos2 hairerWickSquareFourChaos0
  ring

/-- The product of four Wick squares of `Ψ` at several scales is integrable. -/
theorem integrable_hairerPsiWickSquare_four (N : ℕ) (hρ : IsMollifier ρ) {ε : Fin 4 → ℝ}
    {ξ : Fin 4 → Ω → SpaceTime → ℝ} (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i)) (z : Fin 4 → SpaceTime) :
    Integrable (fun ω => hairerPsiWickSquare N ρ (ε 0) (ξ 0) ω (z 0) *
      hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω (z 1) * hairerPsiWickSquare N ρ (ε 2) (ξ 2) ω (z 2) *
      hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω (z 3)) P := by
  have h := hairerPsiField_isCentredGaussianVector_multiscale N hρ hε hW hξ z
  have hi := h.integrable_prod_wickMonomial (L := fun j : Fin 4 => List.replicate 2 j)
  simp only [Fin.prod_univ_four] at hi
  refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [hairerPsiWickSquare_eq_wickMonomial_multiscale N ε ξ z ω 0,
    hairerPsiWickSquare_eq_wickMonomial_multiscale N ε ξ z ω 1,
    hairerPsiWickSquare_eq_wickMonomial_multiscale N ε ξ z ω 2,
    hairerPsiWickSquare_eq_wickMonomial_multiscale N ε ξ z ω 3]
  rfl

/-- The fourth moment of the Wick square: `E[:Ψ²:(z)⁴] = 60 c_ε⁴`. -/
theorem integral_hairerPsiWickSquare_pow_four (N : ℕ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (hW : IsWhiteNoise P W) {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (z : SpaceTime) :
    ∫ ω, hairerPsiWickSquare N ρ ε ξ ω z ^ 4 ∂P = 60 * hairerWickConstant N ρ ε ^ 4 := by
  have h := hairerPsiWickSquare_integral_mul_four N hρ (ε := fun _ => ε) (ξ := fun _ => ξ)
    (fun _ => hε) hW (fun _ => hξ) (fun _ => z)
  simp only [sub_self, hairerCrossCovariance_self] at h
  have hpt : ∀ ω, hairerPsiWickSquare N ρ ε ξ ω z ^ 4 = hairerPsiWickSquare N ρ ε ξ ω z *
      hairerPsiWickSquare N ρ ε ξ ω z * hairerPsiWickSquare N ρ ε ξ ω z *
      hairerPsiWickSquare N ρ ε ξ ω z := fun ω => by ring
  simp_rw [hpt]
  rw [h, ← hairerWickConstant_eq_covariance_zero]
  unfold hairerWickSquareFourChaos4 hairerWickSquareFourChaos2 hairerWickSquareFourChaos0
  ring

/-- The fourth power of the Wick square is integrable. -/
theorem integrable_hairerPsiWickSquare_pow_four (N : ℕ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : 0 < ε) (hW : IsWhiteNoise P W) {ξ : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    Integrable (fun ω => hairerPsiWickSquare N ρ ε ξ ω z ^ 4) P := by
  have h := integrable_hairerPsiWickSquare_four N hρ (ε := fun _ => ε) (ξ := fun _ => ξ)
    (fun _ => hε) hW (fun _ => hξ) (fun _ => z)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  ring

/-- **Cross covariances are bounded by the Wick constants:**
`|Q_{ε,ε'}(x)| ≤ (c_ε + c_ε') / 2`. -/
theorem abs_hairerCrossCovariance_le (N : ℕ) (hρ : IsMollifier ρ) {ε ε' : ℝ} (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ ε' ξ') (x : SpaceTime) :
    |hairerCrossCovariance N ρ ε ε' x| ≤
      (hairerWickConstant N ρ ε + hairerWickConstant N ρ ε') / 2 := by
  have := hW.isProbabilityMeasure
  have h := hairerPsiField_isCentredGaussianVector_two_scale N hρ hε hε' hW hξ hξ' x 0
  have h01 := h.integral_mul 0 1
  have h00 := h.integral_mul 0 0
  have h11 := h.integral_mul 1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, sub_zero,
    hairerCrossCovariance_self, ← hairerWickConstant_eq_covariance_zero] at h01 h00 h11
  have i0 := h.integrable_mul 0 0
  have i1 := h.integrable_mul 1 1
  have i01 := h.integrable_mul 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at i0 i1 i01
  rw [← h01]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ω, |hairerPsiField N ξ ω x * hairerPsiField N ξ' ω 0| ∂P
      ≤ ∫ ω, (hairerPsiField N ξ ω x * hairerPsiField N ξ ω x +
          hairerPsiField N ξ' ω 0 * hairerPsiField N ξ' ω 0) / 2 ∂P := by
        refine integral_mono i01.abs ((i0.add i1).div_const 2) fun ω => ?_
        rw [abs_mul]
        nlinarith [sq_nonneg (|hairerPsiField N ξ ω x| - |hairerPsiField N ξ' ω 0|),
          abs_mul_abs_self (hairerPsiField N ξ ω x),
          abs_mul_abs_self (hairerPsiField N ξ' ω 0)]
    _ = _ := by rw [integral_div, integral_add i0 i1, h00, h11]

end RegularityStructures.Phi43

end
