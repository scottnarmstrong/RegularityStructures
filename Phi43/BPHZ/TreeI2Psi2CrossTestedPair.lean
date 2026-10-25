/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossSub
public import Phi43.BPHZ.TreeI2Psi2TestedMoment

/-!
# Pair integrability of the cross-mollifier difference `F_{ρ,ε} - F_{ρ',ε'}` of `I(Ψ²) Ψ²`

For fixed scales the product `D(y) D(ȳ)` of the difference field `D = F_{ρ,ε} - F_{ρ',ε'}` is
integrable on `Ω` with first moment bounded uniformly in `y, ȳ`, and `D(y) ∈ L²`.  These are the
hypotheses of the tested second-moment Fubini theorem (`integral_abs_integral_mul_sq_le`) for the
field `D`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- **Pair integrability and a uniform first-moment bound for the difference field.** -/
theorem hairerI2Psi2Field_sub_pair_integrable_bound_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x : SpaceTime) :
    ∃ M : ℝ, ∀ y y' : SpaceTime,
      Integrable (fun ω => (hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) *
        (hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y')) P ∧
      ∫ ω, |(hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) *
        (hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y')| ∂P ≤ M := by
  set S : ℝ := (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (24 * hairerWickConstant N ρ ε ^ 4) +
          (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (32 * hairerWickConstant N ρ ε ^ 4) +
          (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) *
            (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ ε ^ 2) with hS
  set S' : ℝ := (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (24 * hairerWickConstant N ρ' ε' ^ 4) +
          (2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|) *
            (32 * hairerWickConstant N ρ' ε' ^ 4) +
          (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ' ε' ^ 2) *
            (2 * (∫ w, |hairerKernelTorus N w|) * hairerWickConstant N ρ' ε' ^ 2) with hS'
  have hD : ∀ y : SpaceTime, ∫ ω, (hairerI2Psi2Field N ρ ε ξ x ω y -
      hairerI2Psi2Field N ρ' ε' ξ' x ω y) ^ 2 ∂P ≤ 2 * S + 2 * S' := by
    intro y
    obtain ⟨i1, b1⟩ := hairerI2Psi2Field_sq_integrable_bound N hρ hε hW hξ x y
    obtain ⟨i2, b2⟩ := hairerI2Psi2Field_sq_integrable_bound N hρ' hε' hW hξ' x y
    have hi := (hairerI2Psi2Field_sub_integral_mul_cross N hρ hρ' hε hε' hW hξ hξ' x y y).1
    have hsq : Integrable (fun ω => (hairerI2Psi2Field N ρ ε ξ x ω y -
        hairerI2Psi2Field N ρ' ε' ξ' x ω y) ^ 2) P :=
      hi.congr (Filter.Eventually.of_forall fun ω => by simp only [sq])
    calc ∫ ω, (hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) ^ 2 ∂P
        ≤ ∫ ω, (2 * hairerI2Psi2Field N ρ ε ξ x ω y ^ 2 +
            2 * hairerI2Psi2Field N ρ' ε' ξ' x ω y ^ 2) ∂P :=
          integral_mono hsq ((i1.const_mul 2).add (i2.const_mul 2)) fun ω => by
            nlinarith [sq_nonneg (hairerI2Psi2Field N ρ ε ξ x ω y +
              hairerI2Psi2Field N ρ' ε' ξ' x ω y)]
      _ = 2 * ∫ ω, hairerI2Psi2Field N ρ ε ξ x ω y ^ 2 ∂P +
            2 * ∫ ω, hairerI2Psi2Field N ρ' ε' ξ' x ω y ^ 2 ∂P := by
          rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by linarith
  refine ⟨2 * S + 2 * S', fun y y' => ?_⟩
  have hi := (hairerI2Psi2Field_sub_integral_mul_cross N hρ hρ' hε hε' hW hξ hξ' x y y').1
  refine ⟨hi, ?_⟩
  have h1 := (hairerI2Psi2Field_sub_integral_mul_cross N hρ hρ' hε hε' hW hξ hξ' x y y).1
  have h2 := (hairerI2Psi2Field_sub_integral_mul_cross N hρ hρ' hε hε' hW hξ hξ' x y' y').1
  have i1 : Integrable (fun ω => (hairerI2Psi2Field N ρ ε ξ x ω y -
      hairerI2Psi2Field N ρ' ε' ξ' x ω y) ^ 2) P :=
    h1.congr (Filter.Eventually.of_forall fun ω => by simp only [sq])
  have i2 : Integrable (fun ω => (hairerI2Psi2Field N ρ ε ξ x ω y' -
      hairerI2Psi2Field N ρ' ε' ξ' x ω y') ^ 2) P :=
    h2.congr (Filter.Eventually.of_forall fun ω => by simp only [sq])
  calc ∫ ω, |(hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) *
        (hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y')| ∂P
      ≤ ∫ ω, ((hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) ^ 2 +
          (hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y') ^ 2) / 2 ∂P :=
        integral_mono hi.abs ((i1.add i2).div_const 2) fun ω => by
          rw [abs_mul]
          nlinarith [sq_nonneg (|hairerI2Psi2Field N ρ ε ξ x ω y -
              hairerI2Psi2Field N ρ' ε' ξ' x ω y| -
              |hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y'|),
            sq_abs (hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y),
            sq_abs (hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y')]
    _ = (∫ ω, (hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) ^ 2 ∂P +
          ∫ ω, (hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y') ^ 2 ∂P) / 2 := by
        rw [integral_div, integral_add i1 i2]
    _ ≤ _ := by linarith [hD y, hD y']

/-- The difference field is square integrable. -/
theorem hairerI2Psi2Field_sub_memLp_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (hε : 0 < ε) (hε' : 0 < ε')
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x y : SpaceTime) :
    MemLp (fun ω => hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) 2 P := by
  have hm : Measurable (fun ω => hairerI2Psi2Field N ρ ε ξ x ω y -
      hairerI2Psi2Field N ρ' ε' ξ' x ω y) :=
    ((Measurable.comp (g := fun q : Ω × SpaceTime => hairerI2Psi2Field N ρ ε ξ x q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_hairerI2Psi2Field_uncurry N hξ x)
      (measurable_id.prodMk measurable_const)).sub
      (Measurable.comp (g := fun q : Ω × SpaceTime => hairerI2Psi2Field N ρ' ε' ξ' x q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_hairerI2Psi2Field_uncurry N hξ' x)
      (measurable_id.prodMk measurable_const)))
  have hi := (hairerI2Psi2Field_sub_integral_mul_cross N hρ hρ' hε hε' hW hξ hξ' x y y).1
  have hsq : Integrable (fun ω => (hairerI2Psi2Field N ρ ε ξ x ω y -
      hairerI2Psi2Field N ρ' ε' ξ' x ω y) ^ 2) P :=
    hi.congr (Filter.Eventually.of_forall fun ω => by simp only [sq])
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hsq

end RegularityStructures.Phi43

end
