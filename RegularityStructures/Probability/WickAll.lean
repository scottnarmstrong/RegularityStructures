/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianMoments
public import RegularityStructures.Probability.GaussianVector
public import RegularityStructures.Probability.Isserlis
public import RegularityStructures.Probability.SpaceTimeMeasure
public import RegularityStructures.Probability.RandomFieldFubini

/-!
# Gaussian moments and Wick calculus

Aggregator for the Gaussian layer:

* `GaussianMoments`: `E[Y⁴] = 3 E[Y²]²`, `E[Y⁶] = 15 E[Y²]³` and vanishing odd moments for a
  centred real Gaussian;
* `GaussianVector`: linear forms of a centred Gaussian vector, symmetry of its law, vanishing of
  odd functionals;
* `Isserlis`: the four-point Isserlis–Wick formula and the covariance of Wick squares;
* `WickPowers`: the covariance of Wick cubes and orthogonality of Wick powers of degree `≤ 3`;
* `SpaceTimeMeasure`: translation and reflection invariance of the measure on `ℝ × T³`;
* `RandomFieldFubini`: exchanging an expectation with a kernel integral.
-/
