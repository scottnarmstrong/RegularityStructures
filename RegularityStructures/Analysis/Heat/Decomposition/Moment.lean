/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Vanishing

/-!
# Moments of the heat shells

`∫ z^l D^k (heatShell n)(z) dz = 2^{(3 + |k|_𝔰 - 5 - |l|_𝔰) n} ∫ w^l D^k (heatShell 0)(w) dw`,
and the integral vanishes unless `k ≤ l` componentwise, by integration by parts.  Hence
`|∫ z^l D^k (heatShell n)| ≤ C 2^{-2n}` [Hai14, (5.5)] with `β = 2`.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem monoFn_parabolicDilate (l : Fin 4 →₀ ℕ) (d : ℝ) (z : ParabolicSpace) :
    monoFn l (parabolicDilate d z) = d ^ multiDeg l * monoFn l z := by
  rw [← evalParabolic_monomial_eq, ← evalParabolic_monomial_eq]
  exact evalParabolic_parabolicDilate (n := multiDeg l)
    (MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl) d z

end RegularityStructures

end
