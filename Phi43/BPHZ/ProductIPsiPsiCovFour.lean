/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PsiGaussianVector
public import Phi43.BPHZ.TreePsiField
public import RegularityStructures.BPHZ.GaussianIsserlis

/-!
# Design note: covariance layer of `I(Ψ)Ψ` and `I(Ψ)(Ψ² - c₁)` (single model)

For `v(y) = ∫ T_{x,y}(w) Ψ(w) dw` (`T = hairerTaylorKernel`, `v = v₁ = hairerIPsiRecentred`) the
field is `F(y) = v(y) Ψ(proj y)`.  The covariance layer is organised as follows.

* `ProductIPsiPsiCovFour` (this file): the four-point Gaussian formula for `Ψ` and its uniform
  `L¹` bound `3 Q(0)²`.
* the identity `E[F F'] = A A' + B Q(d) + R R'` with `A = ∫ T Q(· - proj y)`, `B = E[v v']`,
  `R = ∫ T Q(· - proj y')` (Fubini for tested pairs + the four-point formula);
* a refined pointwise majorant of `T` (`r ≤ 1/2`) and a crude one (all `r`), giving the key bound
  `|∫ T_y(w) Q(w - g) dw| ≲ W(r) (1 + s(proj x - g)^(-θ))`;
* `E v² ≲ r^(3-δ)` for all `r`, so `|B| ≲ r^((3-δ)/2) r'^((3-δ)/2)`;
* the pointwise majorant `|E F F'| ≲ W W' (1 + e₁^(-θ))(1 + e₂^(-θ)) + V V' d^(-1)`;
* periodisation of the `ℝ⁴ × ℝ⁴` integral against a weighted semigroup test profile and the double
  bounds of `SemigroupTestProfile`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- **Four-point formula for `Ψ`**, with integrability. -/
theorem hairerPsiField_integral_mul_four (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (a b c d : SpaceTime) :
    Integrable (fun ω => hairerPsiField N ξ ω a * hairerPsiField N ξ ω b *
      hairerPsiField N ξ ω c * hairerPsiField N ξ ω d) P ∧
    ∫ ω, hairerPsiField N ξ ω a * hairerPsiField N ξ ω b * hairerPsiField N ξ ω c *
      hairerPsiField N ξ ω d ∂P =
      hairerCovariance N ρ ε (a - b) * hairerCovariance N ρ ε (c - d) +
        hairerCovariance N ρ ε (a - c) * hairerCovariance N ρ ε (b - d) +
        hairerCovariance N ρ ε (a - d) * hairerCovariance N ρ ε (b - c) := by
  have h := hairerPsiField_isCentredGaussianVector N hρ hε hW hξ ![a, b, c, d]
  have hP := h.isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · have := h.integrable_prod_apply (σ := fun i : Fin 4 => i) Finset.univ
    simpa [Fin.prod_univ_four, mul_assoc] using this
  · have e : ∀ ω, hairerPsiField N ξ ω a * hairerPsiField N ξ ω b * hairerPsiField N ξ ω c *
        hairerPsiField N ξ ω d =
        (fun ω (i : Fin 4) => hairerPsiField N ξ ω (![a, b, c, d] i)) ω 0 *
          ∏ k ∈ ({1, 2, 3} : Finset (Fin 4)),
            (fun ω (i : Fin 4) => hairerPsiField N ξ ω (![a, b, c, d] i)) ω k := by
      intro ω
      simp [Finset.prod_insert, mul_assoc]
    simp_rw [e]
    rw [h.integral_mul_prod_eq_sum (σ := fun i : Fin 4 => i) 0 ({1, 2, 3} : Finset (Fin 4))]
    have e1 : ({1, 2, 3} : Finset (Fin 4)).erase 1 = {2, 3} := by decide
    have e2 : ({1, 2, 3} : Finset (Fin 4)).erase 2 = {1, 3} := by decide
    have e3 : ({1, 2, 3} : Finset (Fin 4)).erase 3 = {1, 2} := by decide
    have s2 := hairerPsiField_integral_mul N hρ hε hW hξ
    have hsum : ∑ j ∈ ({1, 2, 3} : Finset (Fin 4)), hairerCovariance N ρ ε (![a, b, c, d] 0 - ![a, b, c, d] j) *
        ∫ ω, ∏ k ∈ ({1, 2, 3} : Finset (Fin 4)).erase j,
          hairerPsiField N ξ ω (![a, b, c, d] k) ∂P =
        hairerCovariance N ρ ε (a - b) * ∫ ω, ∏ k ∈ ({2, 3} : Finset (Fin 4)),
          hairerPsiField N ξ ω (![a, b, c, d] k) ∂P +
        hairerCovariance N ρ ε (a - c) * ∫ ω, ∏ k ∈ ({1, 3} : Finset (Fin 4)),
          hairerPsiField N ξ ω (![a, b, c, d] k) ∂P +
        hairerCovariance N ρ ε (a - d) * ∫ ω, ∏ k ∈ ({1, 2} : Finset (Fin 4)),
          hairerPsiField N ξ ω (![a, b, c, d] k) ∂P := by
      rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide), e1, e2, e3]
      simp [add_assoc]
    simp only [hsum]
    simp only [Finset.prod_pair (show (2 : Fin 4) ≠ 3 by decide),
      Finset.prod_pair (show (1 : Fin 4) ≠ 3 by decide),
      Finset.prod_pair (show (1 : Fin 4) ≠ 2 by decide)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [s2, s2, s2]

/-- `|a b c d| ≤ (a⁴ + b⁴ + c⁴ + d⁴) / 4`. -/
theorem abs_mul_four_le_pow_four (p q r s : ℝ) :
    |p * q * r * s| ≤ (p ^ 4 + q ^ 4 + r ^ 4 + s ^ 4) / 4 := by
  have h1 : |p * q| ≤ (p ^ 2 + q ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p + q), sq_nonneg (p - q)]
  have h2 : |r * s| ≤ (r ^ 2 + s ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (r + s), sq_nonneg (r - s)]
  have h3 : |p * q| * |r * s| ≤ ((p ^ 2 + q ^ 2) / 2) * ((r ^ 2 + s ^ 2) / 2) :=
    mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have h4 : ((p ^ 2 + q ^ 2) / 2) * ((r ^ 2 + s ^ 2) / 2) ≤
      (p ^ 4 + q ^ 4 + r ^ 4 + s ^ 4) / 4 := by
    nlinarith [sq_nonneg (p ^ 2 - r ^ 2), sq_nonneg (p ^ 2 - s ^ 2), sq_nonneg (q ^ 2 - r ^ 2),
      sq_nonneg (q ^ 2 - s ^ 2)]
  calc |p * q * r * s| = |p * q| * |r * s| := by rw [← abs_mul]; ring_nf
    _ ≤ _ := h3.trans h4

/-- `E Ψ(z)⁴ = 3 Q(0)²`. -/
theorem hairerPsiField_integral_pow_four (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    ∫ ω, hairerPsiField N ξ ω z ^ 4 ∂P = 3 * hairerCovariance N ρ ε 0 ^ 2 := by
  have h := (hairerPsiField_integral_mul_four N hρ hε hW hξ z z z z).2
  simp only [sub_self] at h
  rw [show (fun ω => hairerPsiField N ξ ω z ^ 4) = fun ω => hairerPsiField N ξ ω z *
    hairerPsiField N ξ ω z * hairerPsiField N ξ ω z * hairerPsiField N ξ ω z from
    funext fun ω => by ring, h]
  ring

/-- **Uniform `L¹` bound** `E |Ψ(a) Ψ(b) Ψ(c) Ψ(d)| ≤ 3 Q(0)²`. -/
theorem hairerPsiField_integral_abs_mul_four_le (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (a b c d : SpaceTime) :
    ∫ ω, |hairerPsiField N ξ ω a * hairerPsiField N ξ ω b * hairerPsiField N ξ ω c *
      hairerPsiField N ξ ω d| ∂P ≤ 3 * hairerCovariance N ρ ε 0 ^ 2 := by
  have hi : ∀ z, Integrable (fun ω => hairerPsiField N ξ ω z ^ 4) P := fun z => by
    have := (hairerPsiField_integral_mul_four N hρ hε hW hξ z z z z).1
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hm := (hairerPsiField_integral_mul_four N hρ hε hW hξ a b c d).1
  have hab : Integrable (fun ω => hairerPsiField N ξ ω a ^ 4 + hairerPsiField N ξ ω b ^ 4) P :=
    (hi a).add (hi b)
  have habc : Integrable (fun ω => hairerPsiField N ξ ω a ^ 4 + hairerPsiField N ξ ω b ^ 4 +
      hairerPsiField N ξ ω c ^ 4) P := hab.add (hi c)
  have hsum : Integrable (fun ω => hairerPsiField N ξ ω a ^ 4 + hairerPsiField N ξ ω b ^ 4 +
      hairerPsiField N ξ ω c ^ 4 + hairerPsiField N ξ ω d ^ 4) P := habc.add (hi d)
  calc ∫ ω, |hairerPsiField N ξ ω a * hairerPsiField N ξ ω b * hairerPsiField N ξ ω c *
        hairerPsiField N ξ ω d| ∂P
      ≤ ∫ ω, (hairerPsiField N ξ ω a ^ 4 + hairerPsiField N ξ ω b ^ 4 +
          hairerPsiField N ξ ω c ^ 4 + hairerPsiField N ξ ω d ^ 4) / 4 ∂P := by
        refine integral_mono hm.abs (hsum.div_const 4) fun ω => ?_
        exact abs_mul_four_le_pow_four _ _ _ _
    _ = 3 * hairerCovariance N ρ ε 0 ^ 2 := by
        rw [integral_div, integral_add habc (hi d), integral_add hab (hi c), integral_add (hi a) (hi b)]
        simp only [hairerPsiField_integral_pow_four N hρ hε hW hξ]
        ring

/-- Two-point integrability and the uniform bound `E |Ψ(a) Ψ(b)| ≤ Q(0)`. -/
theorem hairerPsiField_integral_abs_mul_two_le (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (a b : SpaceTime) :
    Integrable (fun ω => hairerPsiField N ξ ω a * hairerPsiField N ξ ω b) P ∧
    ∫ ω, |hairerPsiField N ξ ω a * hairerPsiField N ξ ω b| ∂P ≤ hairerCovariance N ρ ε 0 := by
  have hm : Integrable (fun ω => hairerPsiField N ξ ω a * hairerPsiField N ξ ω b) P :=
    (hairerPsiField_memLp N hρ hε hW hξ a).integrable_mul (hairerPsiField_memLp N hρ hε hW hξ b)
  have hsa : Integrable (fun ω => hairerPsiField N ξ ω a * hairerPsiField N ξ ω a) P :=
    (hairerPsiField_memLp N hρ hε hW hξ a).integrable_mul (hairerPsiField_memLp N hρ hε hW hξ a)
  have hsb : Integrable (fun ω => hairerPsiField N ξ ω b * hairerPsiField N ξ ω b) P :=
    (hairerPsiField_memLp N hρ hε hW hξ b).integrable_mul (hairerPsiField_memLp N hρ hε hW hξ b)
  refine ⟨hm, ?_⟩
  calc ∫ ω, |hairerPsiField N ξ ω a * hairerPsiField N ξ ω b| ∂P
      ≤ ∫ ω, (hairerPsiField N ξ ω a * hairerPsiField N ξ ω a +
          hairerPsiField N ξ ω b * hairerPsiField N ξ ω b) / 2 ∂P := by
        refine integral_mono hm.abs ((hsa.add hsb).div_const 2) fun ω => ?_
        rw [abs_le]; constructor <;>
          nlinarith [sq_nonneg (hairerPsiField N ξ ω a + hairerPsiField N ξ ω b),
            sq_nonneg (hairerPsiField N ξ ω a - hairerPsiField N ξ ω b)]
    _ = hairerCovariance N ρ ε 0 := by
        rw [integral_div, integral_add hsa hsb, hairerPsiField_integral_mul N hρ hε hW hξ,
          hairerPsiField_integral_mul N hρ hε hW hξ]
        simp

end RegularityStructures.Phi43

end
