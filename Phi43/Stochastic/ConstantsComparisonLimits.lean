/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonWick
public import Phi43.Stochastic.ConstantsComparisonSunset

/-!
# Comparison of the renormalisation constants for the causal Hairer kernel

The first two comparisons relate the massive-torus constants to the causal truncated-kernel
versions of [Hai14, (10.33), (10.41)]. Both limits are defined without a mollifier. The third is
their linear combination, with the coefficients of [Hai14, (9.21)]. All three results assume only
`IsMollifier ρ` and the shell moment parameter `N`; every analytic estimate is proved.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.Phi43

/-- The finite change of mass convention, independent of `ρ`. -/
def constantsComparison_countertermLimit (N : ℕ) : ℝ :=
  3 * constantsComparison_wickLimit N - 9 * constantsComparison_sunsetLimit N

/-- The difference of the two mass counterterms converges to the same constant for every
mollifier. The two coefficients are those in Hairer (9.21). -/
theorem constantsComparison_countertermLimit_tendsto
    (N : ℕ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    Tendsto
      (fun ε : ℝ => 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε -
        (3 * hairerWickConstant N ρ ε - 9 * hairerSunsetConstant N ρ ε))
      (𝓝[>] 0) (𝓝 (constantsComparison_countertermLimit N)) :=
  constantsComparison_counterterm_tendsto
    (constantsComparison_wickLimit_tendsto N ρ hρ) (constantsComparison_sunsetLimit_tendsto N ρ hρ)

/-- Comparison of the renormalisation constants, with the quantifiers making mollifier
independence explicit: the limits are chosen before the mollifier. -/
theorem constantsComparison_limits (N : ℕ) :
    ∃ L₁ L₂ κ : ℝ, ∀ (ρ : ParabolicSpace → ℝ), IsMollifier ρ →
      Tendsto (fun ε : ℝ => wickConstant ρ ε - hairerWickConstant N ρ ε)
        (𝓝[>] 0) (𝓝 L₁) ∧
      Tendsto (fun ε : ℝ => sunsetConstant ρ ε - hairerSunsetConstant N ρ ε)
        (𝓝[>] 0) (𝓝 L₂) ∧
      Tendsto
        (fun ε : ℝ => 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε -
          (3 * hairerWickConstant N ρ ε - 9 * hairerSunsetConstant N ρ ε))
        (𝓝[>] 0) (𝓝 κ) := by
  refine ⟨constantsComparison_wickLimit N, constantsComparison_sunsetLimit N,
    constantsComparison_countertermLimit N, ?_⟩
  intro ρ hρ
  exact ⟨constantsComparison_wickLimit_tendsto N ρ hρ, constantsComparison_sunsetLimit_tendsto N ρ hρ,
    constantsComparison_countertermLimit_tendsto N ρ hρ⟩

end RegularityStructures.Phi43

end
