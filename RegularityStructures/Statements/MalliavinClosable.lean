/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureAutomaticClosable

/-!
# Closability of the white-noise derivative

The statement `RegularityStructures.Statements.malliavin_derivative_closable`.
Its proof is `RegularityStructures.malliavin_derivative_closable`,
in the module `RegularityStructures.Probability.MalliavinClosureAutomaticClosable`.
-/

public section

namespace RegularityStructures

/-- **Closability of the Malliavin derivative** [HS23, Definition 2.20 and Remark 2.22]: for a white
noise `W`, a sequence of cylindrical graph points converging to `(0, G)` in `L² × L²` has `G =
0`. -/
theorem Statements.malliavin_derivative_closable.{u_1} :
    ∀ {Ω : Type u_1} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
      {W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ},
      RegularityStructures.IsWhiteNoise P W →
        ∀ {G : ↥(MeasureTheory.Lp ℝ 2 (RegularityStructures.whiteNoiseDerivativeMeasure P))}
          (q :
            ℕ → ↥(MeasureTheory.Lp ℝ 2 P) × ↥(MeasureTheory.Lp ℝ 2 (RegularityStructures.whiteNoiseDerivativeMeasure P))),
          (∀ (n : ℕ), q n ∈ RegularityStructures.cylindricalMalliavinGraph P W) →
            Filter.Tendsto (fun (n : ℕ) => (q n).1) Filter.atTop (nhds 0) →
              Filter.Tendsto (fun (n : ℕ) => (q n).2) Filter.atTop (nhds G) → G = 0 :=
  by exact RegularityStructures.malliavin_derivative_closable

end RegularityStructures

end
