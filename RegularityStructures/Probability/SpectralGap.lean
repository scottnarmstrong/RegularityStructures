/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.WhiteNoise
public import RegularityStructures.Probability.Poincare
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Covariance

/-!
# Cylindrical derivatives for white noise

This module records the covariance energy and the literal cylindrical derivative used in the
white-noise spectral-gap estimate. The finite-dimensional Gaussian and spectral-gap inequalities are
stated as theorems in the adjoining probability modules; no proposition-valued target or
admissibility record is used here. The stochastic interpretation follows [HS23, Definition 2.20 and
Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

/-- The quadratic covariance energy `⟪v, C v⟫`, in the `Fin n → ℝ` convention. -/
def covarianceEnergy {n : ℕ} (C : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, v i * ∑ j, C i j * v j

end RegularityStructures

end
