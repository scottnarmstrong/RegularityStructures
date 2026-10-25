/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeWickDifferenceCov
public import Phi43.BPHZ.TreePsiDifference
public import Phi43.BPHZ.PsiGaussianVector

/-!
# Measurability of the cross covariance

`measurable_hairerCrossCovariance`: the cross covariance `Q_{ε,ε'}` of the fields `Ψ_ε`, `Ψ_ε'`
of two regularised noises of the same white noise is measurable. It enters the second moments of
the tested differences of Wick powers at two scales [Hai14, (10.3) for `τ = Ψ²`, `Ψ³`].
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The cross covariance `Q_{ε,ε'}` is measurable. -/
theorem measurable_hairerCrossCovariance (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (ε ε' : ℝ) :
    Measurable (hairerCrossCovariance N ρ ε ε') := by
  have hint : Measurable (fun q : SpaceTime × SpaceTime =>
      hairerMollifiedKernel N ρ ε (q.1 + q.2) * hairerMollifiedKernel N ρ ε' q.2) :=
    ((measurable_hairerMollifiedKernel N hρ ε).comp (measurable_fst.add measurable_snd)).mul
      ((measurable_hairerMollifiedKernel N hρ ε').comp measurable_snd)
  exact hint.stronglyMeasurable.integral_prod_right'.measurable

end RegularityStructures.Phi43

end
