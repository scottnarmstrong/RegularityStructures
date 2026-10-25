/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossCov

/-!
# The tree `I(Ψ²) Ψ²`: covariance of the cross-mollifier difference

For mollifiers `ρ, ρ'`, scales `a`, `b` and noises `ξ`, `ξ'` of the same white noise,
`E[(F_{ρ,a} - F_{ρ',b})(y) (F_{ρ,a} - F_{ρ',b})(y')]` is the second difference
`Cov(ρa,ρa) - Cov(ρa,ρ'b) - Cov(ρ'b,ρa) + Cov(ρ'b,ρ'b)` of `hairerI2Psi2CovTwo`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- **Covariance of the two-scale difference of the field `(10.39)`.** -/
theorem hairerI2Psi2Field_sub_integral_mul_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ' b ξ')
    (x y y' : SpaceTime) :
    Integrable (fun ω => (hairerI2Psi2Field N ρ a ξ x ω y - hairerI2Psi2Field N ρ' b ξ' x ω y) *
      (hairerI2Psi2Field N ρ a ξ x ω y' - hairerI2Psi2Field N ρ' b ξ' x ω y')) P ∧
    ∫ ω, (hairerI2Psi2Field N ρ a ξ x ω y - hairerI2Psi2Field N ρ' b ξ' x ω y) *
        (hairerI2Psi2Field N ρ a ξ x ω y' - hairerI2Psi2Field N ρ' b ξ' x ω y') ∂P =
      hairerI2Psi2CovTwo N ρ ρ x a a y y' - hairerI2Psi2CovTwo N ρ ρ' x a b y y' -
        hairerI2Psi2CovTwo N ρ' ρ x b a y y' + hairerI2Psi2CovTwo N ρ' ρ' x b b y y' := by
  obtain ⟨i1, e1⟩ := hairerI2Psi2Field_integral_mul_cross N hρ hρ ha ha hW hξ hξ x y y'
  obtain ⟨i2, e2⟩ := hairerI2Psi2Field_integral_mul_cross N hρ hρ' ha hb hW hξ hξ' x y y'
  obtain ⟨i3, e3⟩ := hairerI2Psi2Field_integral_mul_cross N hρ' hρ hb ha hW hξ' hξ x y y'
  obtain ⟨i4, e4⟩ := hairerI2Psi2Field_integral_mul_cross N hρ' hρ' hb hb hW hξ' hξ' x y y'
  have hpt : ∀ ω, (hairerI2Psi2Field N ρ a ξ x ω y - hairerI2Psi2Field N ρ' b ξ' x ω y) *
      (hairerI2Psi2Field N ρ a ξ x ω y' - hairerI2Psi2Field N ρ' b ξ' x ω y') =
      hairerI2Psi2Field N ρ a ξ x ω y * hairerI2Psi2Field N ρ a ξ x ω y' -
        hairerI2Psi2Field N ρ a ξ x ω y * hairerI2Psi2Field N ρ' b ξ' x ω y' -
        hairerI2Psi2Field N ρ' b ξ' x ω y * hairerI2Psi2Field N ρ a ξ x ω y' +
        hairerI2Psi2Field N ρ' b ξ' x ω y * hairerI2Psi2Field N ρ' b ξ' x ω y' :=
    fun ω => by ring
  have j1 : Integrable (fun ω => hairerI2Psi2Field N ρ a ξ x ω y *
      hairerI2Psi2Field N ρ a ξ x ω y' - hairerI2Psi2Field N ρ a ξ x ω y *
      hairerI2Psi2Field N ρ' b ξ' x ω y') P := i1.sub i2
  have j2 : Integrable (fun ω => hairerI2Psi2Field N ρ a ξ x ω y *
      hairerI2Psi2Field N ρ a ξ x ω y' - hairerI2Psi2Field N ρ a ξ x ω y *
      hairerI2Psi2Field N ρ' b ξ' x ω y' - hairerI2Psi2Field N ρ' b ξ' x ω y *
      hairerI2Psi2Field N ρ a ξ x ω y') P := j1.sub i3
  simp_rw [hpt]
  refine ⟨j2.add i4, ?_⟩
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2, e1, e2, e3, e4]
  rfl

end RegularityStructures.Phi43

end
