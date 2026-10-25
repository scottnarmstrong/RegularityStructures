/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2Field
public import Phi43.BPHZ.TreeWickSquare
public import Phi43.BPHZ.TreeWickCube
public import RegularityStructures.Probability.RandomFieldFubini
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# The tree `I(Ψ³) Ψ²`: the mean

The field `hairerI3Psi2Field` lies in the odd chaoses `1, 3, 5`, so `E[(Π̂^ε_x τ)(y)] = 0`.
Concretely `:Ψ³:(w) :Ψ²:(y)` is an odd function of the Gaussian vector `(Ψ(w), Ψ(y))`, hence
centred; by stochastic Fubini `E[(∫ g :Ψ³:) :Ψ²:(y)] = 0` for `g ∈ L¹`; and `Ψ(y)` is centred. The
generic Fubini step `integral_integral_mul_mul_swap_field` (`E[(∫ g Y) B] = ∫ g E[Y B]`) is reused
for the cross terms with the counterterm `-3 C₂ Ψ`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- **Fubini for a kernel against a product field.** If `Y` is jointly measurable, `B` is measurable,
each `Y(w) B` is integrable with `E|Y(w) B| ≤ M` uniformly, and `g ∈ L¹`, then
`E[(∫ g Y) B] = ∫ g(w) E[Y(w) B] dw` and `(∫ g Y) B` is integrable. -/
theorem integral_integral_mul_mul_swap_field [IsProbabilityMeasure P] {Y : Ω → SpaceTime → ℝ}
    {B : Ω → ℝ} (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2) (hB : Measurable B)
    {g : SpaceTime → ℝ} (hg : Integrable g) {M : ℝ}
    (hi : ∀ w, Integrable (fun ω => Y ω w * B ω) P)
    (hM : ∀ w, ∫ ω, |Y ω w * B ω| ∂P ≤ M) :
    Integrable (fun ω => (∫ w, g w * Y ω w) * B ω) P ∧
      ∫ ω, (∫ w, g w * Y ω w) * B ω ∂P = ∫ w, g w * ∫ ω, Y ω w * B ω ∂P := by
  have hY' : AEStronglyMeasurable (Function.uncurry fun ω w => Y ω w * B ω) (P.prod volume) :=
    (hY.mul (hB.comp measurable_fst)).aestronglyMeasurable
  have hG := integrable_uncurry_mul_of_bound (P := P) (μ := (volume : Measure SpaceTime)) hg hY'
    hi hM
  have hpt : ∀ ω, (∫ w, g w * Y ω w) * B ω = ∫ w, g w * (Y ω w * B ω) := by
    intro ω
    rw [← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => by simp only; ring)
  refine ⟨?_, ?_⟩
  · refine (hG.integral_prod_left).congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (hpt ω).symm
  · simp_rw [hpt]
    exact integral_integral_mul_swap hg hY' hi hM

end RegularityStructures.Phi43

end
