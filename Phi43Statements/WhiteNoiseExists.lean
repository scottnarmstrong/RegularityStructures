/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.WhiteNoiseExists

/-!
# Existence of space-time white noise

Some probability space carries a space-time white noise on `ℝ × T³` in the sense of Definition 2.2
of the statement (`IsWhiteNoise`).

This is item (W1) of Lemma 4.1 of the statement. Items (W1)–(W5) show that Theorem A is not vacuous:
the white noises, regularised noises and classical solutions over which it quantifies exist, and its
conditions are meaningful.

The proof is `RegularityStructures.exists_whiteNoise`,
in the module `RegularityStructures.Probability.WhiteNoiseExists`.

Source: the statement, Lemma 4.1 (W1).
-/

public section

namespace RegularityStructures.Phi43.Statements

open MeasureTheory Set
open scoped ENNReal

/-- **Existence of white noise** (Lemma 4.1 (W1)). Some probability space carries a
space-time white noise. -/
theorem exists_whiteNoise :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ),
      IsProbabilityMeasure P ∧ IsWhiteNoise P W :=
  by exact RegularityStructures.exists_whiteNoise

end RegularityStructures.Phi43.Statements

end
