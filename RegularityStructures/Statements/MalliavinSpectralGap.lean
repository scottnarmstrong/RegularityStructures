/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureSpectralGap

/-!
# The spectral gap on `D^{1,2}`

The statement `RegularityStructures.Statements.malliavin_spectral_gap`.
Its proof is `RegularityStructures.malliavin_spectral_gap`,
in the module `RegularityStructures.Probability.MalliavinClosureSpectralGap`.
-/

public section

namespace RegularityStructures

/-- **The spectral gap inequality** on the closure `D^{1,2}` of the cylindrical white-noise
functionals: `Var F ≤ ‖DF‖²`. -/
theorem Statements.malliavin_spectral_gap.{u_1} :
    ∀ {Ω : Type u_1} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
      [MeasureTheory.IsProbabilityMeasure P] {W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ},
      RegularityStructures.IsWhiteNoise P W →
        ∀ (u : ↑(RegularityStructures.MalliavinSobolev P W)),
          RegularityStructures.malliavinVariance P (RegularityStructures.malliavinValue u) ≤
            ‖RegularityStructures.malliavinDerivative u‖ ^ 2 :=
  by exact RegularityStructures.malliavin_spectral_gap

end RegularityStructures

end
