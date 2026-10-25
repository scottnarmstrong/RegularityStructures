/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoCov
public import Phi43.BPHZ.TreeI3Psi2TestedMoment

/-!
# Qualitative moment facts for the difference of the fields of `I(Ψ³) Ψ²`

For the fields `F` at `(ρ, ε)` and `F'` at `(ρ', ε')`, the difference `G = F - F'` is jointly
measurable, square integrable at every point and its pair products `G(y) G(y')` are integrable with
first moment bounded uniformly in `y, y'` (for fixed `ε, ε'`).  These are the hypotheses of the
tested second-moment Fubini theorem `integral_abs_integral_mul_sq_le`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- Joint measurability of the difference of the fields. -/
theorem measurable_hairerI3Psi2Field_sub_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x : SpaceTime) :
    Measurable (fun q : Ω × SpaceTime =>
      hairerI3Psi2Field N ρ ε ξ x q.1 q.2 - hairerI3Psi2Field N ρ' ε' ξ' x q.1 q.2) :=
  (measurable_hairerI3Psi2Field_uncurry N hξ x).sub (measurable_hairerI3Psi2Field_uncurry N hξ' x)

/-- The difference of the fields is square integrable at every point. -/
theorem hairerI3Psi2Field_sub_memLp (N : ℕ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x w : SpaceTime) :
    MemLp (fun ω => hairerI3Psi2Field N ρ ε ξ x ω w - hairerI3Psi2Field N ρ' ε' ξ' x ω w) 2 P :=
  (hairerI3Psi2Field_memLp N hρ hε hW hξ x w).sub (hairerI3Psi2Field_memLp N hρ' hε' hW hξ' x w)

private theorem abs_mul_le_half_sq_add'' (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 :=
  abs_le.2 ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩

/-- **Pair integrability and a uniform first-moment bound for the difference of the fields.** -/
theorem hairerI3Psi2Field_sub_pair_integrable_bound (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x : SpaceTime) :
    ∃ M : ℝ, ∀ y y' : SpaceTime,
      Integrable (fun ω => (hairerI3Psi2Field N ρ ε ξ x ω y - hairerI3Psi2Field N ρ' ε' ξ' x ω y) *
        (hairerI3Psi2Field N ρ ε ξ x ω y' - hairerI3Psi2Field N ρ' ε' ξ' x ω y')) P ∧
      ∫ ω, |(hairerI3Psi2Field N ρ ε ξ x ω y - hairerI3Psi2Field N ρ' ε' ξ' x ω y) *
        (hairerI3Psi2Field N ρ ε ξ x ω y' - hairerI3Psi2Field N ρ' ε' ξ' x ω y')| ∂P ≤ M := by
  obtain ⟨M₁, hM₁⟩ := exists_hairerI3Psi2Field_sq_integral_le N hρ hε hW hξ x
  obtain ⟨M₂, hM₂⟩ := exists_hairerI3Psi2Field_sq_integral_le N hρ' hε' hW hξ' x
  have hsq : ∀ y, Integrable (fun ω => (hairerI3Psi2Field N ρ ε ξ x ω y -
      hairerI3Psi2Field N ρ' ε' ξ' x ω y) ^ 2) P ∧
      ∫ ω, (hairerI3Psi2Field N ρ ε ξ x ω y - hairerI3Psi2Field N ρ' ε' ξ' x ω y) ^ 2 ∂P ≤
        2 * M₁ + 2 * M₂ := by
    intro y
    obtain ⟨i1, b1⟩ := hM₁ y
    obtain ⟨i2, b2⟩ := hM₂ y
    have hpt : ∀ ω, (hairerI3Psi2Field N ρ ε ξ x ω y - hairerI3Psi2Field N ρ' ε' ξ' x ω y) ^ 2 ≤
        2 * hairerI3Psi2Field N ρ ε ξ x ω y ^ 2 + 2 * hairerI3Psi2Field N ρ' ε' ξ' x ω y ^ 2 :=
      fun ω => by nlinarith [sq_nonneg (hairerI3Psi2Field N ρ ε ξ x ω y +
        hairerI3Psi2Field N ρ' ε' ξ' x ω y)]
    have hi : Integrable (fun ω => (hairerI3Psi2Field N ρ ε ξ x ω y -
        hairerI3Psi2Field N ρ' ε' ξ' x ω y) ^ 2) P :=
      (hairerI3Psi2Field_sub_memLp N hρ hρ' hε hε' hW hξ hξ' x y).integrable_sq
    refine ⟨hi, ?_⟩
    calc _ ≤ ∫ ω, (2 * hairerI3Psi2Field N ρ ε ξ x ω y ^ 2 +
          2 * hairerI3Psi2Field N ρ' ε' ξ' x ω y ^ 2) ∂P :=
        integral_mono hi ((i1.const_mul 2).add (i2.const_mul 2)) hpt
      _ = 2 * ∫ ω, hairerI3Psi2Field N ρ ε ξ x ω y ^ 2 ∂P +
          2 * ∫ ω, hairerI3Psi2Field N ρ' ε' ξ' x ω y ^ 2 ∂P := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
          integral_const_mul]
      _ ≤ _ := by linarith
  refine ⟨2 * M₁ + 2 * M₂, fun y y' => ?_⟩
  obtain ⟨i1, b1⟩ := hsq y
  obtain ⟨i2, b2⟩ := hsq y'
  have hint := (hairerI3Psi2Field_sub_integral_mulTwo N hρ hρ' hε hε' hW hξ hξ' x y y').1
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ ω, ((hairerI3Psi2Field N ρ ε ξ x ω y - hairerI3Psi2Field N ρ' ε' ξ' x ω y) ^ 2 +
        (hairerI3Psi2Field N ρ ε ξ x ω y' - hairerI3Psi2Field N ρ' ε' ξ' x ω y') ^ 2) / 2 ∂P :=
        integral_mono hint.abs ((i1.add i2).div_const 2) fun ω => abs_mul_le_half_sq_add'' _ _
    _ = (∫ ω, (hairerI3Psi2Field N ρ ε ξ x ω y - hairerI3Psi2Field N ρ' ε' ξ' x ω y) ^ 2 ∂P +
        ∫ ω, (hairerI3Psi2Field N ρ ε ξ x ω y' - hairerI3Psi2Field N ρ' ε' ξ' x ω y') ^ 2 ∂P) /
          2 := by rw [integral_div, integral_add i1 i2]
    _ ≤ _ := by linarith

end RegularityStructures.Phi43

end
