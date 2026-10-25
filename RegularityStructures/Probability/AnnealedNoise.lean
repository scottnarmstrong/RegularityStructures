/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral
public import RegularityStructures.Probability.SpaceTimeMeasure
public import RegularityStructures.Probability.WhiteNoise

/-!
# Gaussian pairings and the universal-cover test-function estimate

The white-noise definition identifies the second moment of `W g` with the squared `L²` norm of
`g`.  The rescaled test functions used in Hairer [Hai14, (2.13)] have a uniform `L¹` bound;
their pointwise bound therefore gives the expected `λ⁻⁵` estimate on the universal cover.

The torus-valued pairing with a rescaled test function is deliberately not introduced here:
`rescaledTestFunction` lives on `ParabolicSpace`, whereas `IsWhiteNoise` indexes functions on
`SpaceTime`.  A separate periodisation/lift is needed before these two estimates can be joined.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem whiteNoise_pairing_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {g : SpaceTime → ℝ} (hg : MemLp g 2) :
    ∫ ω, (W g ω) ^ 2 ∂P = ∫ z, g z ^ 2 := by
  have hvec := hW.2 1 (fun _ : Fin 1 => g) (by
    intro i
    simpa using hg)
  have hcoord := hvec.2.2.2 0 0
  simpa only [pow_two] using hcoord

theorem whiteNoise_pairing_abs_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {g : SpaceTime → ℝ} (hg : MemLp g 2) :
    ∫ ω, |W g ω| ^ 2 ∂P = ∫ z, g z ^ 2 := by
  rw [show (fun ω => |W g ω| ^ 2) = (fun ω => (W g ω) ^ 2) by
    funext ω
    exact sq_abs _]
  exact whiteNoise_pairing_sq_integral hW hg

end RegularityStructures

end
