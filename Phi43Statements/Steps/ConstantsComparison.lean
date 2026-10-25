/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonLimits

/-!
# Comparison of the renormalisation constants

The constants `C₁^ε`, `C₂^ε` of the statement (Definition 2.5) are built from the massive heat
kernel `G`. Hairer's constants `C₁^{ε,K}`, `C₂^{ε,K}` [Hai14, (10.33), (10.41)] are built from
his truncated kernel `K`. The differences converge as `ε ↓ 0`, to limits that do not depend on the
mollifier: `C₁^ε - C₁^{ε,K} → L₁` and `C₂^ε - C₂^{ε,K} → L₂`. So the two counterterms
`3C₁^ε - 9C₂^ε` and `3C₁^{ε,K} - 9C₂^{ε,K}` differ by a mollifier-independent constant plus
`o(1)`.

In the proof of Theorem A this shows that renormalising with the constants of the statement is,
up to a convergent shift of the mass `a`, the renormalisation of [Hai14, Theorem 10.22]. The
mollifier independence of the limiting model then gives condition (A4).

The proof is `RegularityStructures.Phi43.constantsComparison_limits`,
in the module `Phi43.Stochastic.ConstantsComparisonLimits`.

Source: [Hai14, (10.33), (10.41), Theorem 10.22]; the statement, Definition 2.5.
-/

public section

namespace RegularityStructures.Phi43

open scoped Topology

/-- **Comparison of the constants.** The differences between the constants of the statement
and Hairer's constants converge, to limits that do not depend on the mollifier, and so does the
difference of the two counterterms. -/
theorem Statements.constantsComparison :
    ∀ N : ℕ, ∃ L₁ L₂ κ : ℝ, ∀ (ρ : RegularityStructures.ParabolicSpace → ℝ),
      RegularityStructures.Phi43.IsMollifier ρ →
      Filter.Tendsto (fun ε : ℝ => RegularityStructures.Phi43.wickConstant ρ ε -
          RegularityStructures.Phi43.hairerWickConstant N ρ ε) (𝓝[>] 0) (𝓝 L₁) ∧
      Filter.Tendsto (fun ε : ℝ => RegularityStructures.Phi43.sunsetConstant ρ ε -
          RegularityStructures.Phi43.hairerSunsetConstant N ρ ε) (𝓝[>] 0) (𝓝 L₂) ∧
      Filter.Tendsto
        (fun ε : ℝ => 3 * RegularityStructures.Phi43.wickConstant ρ ε -
            9 * RegularityStructures.Phi43.sunsetConstant ρ ε -
          (3 * RegularityStructures.Phi43.hairerWickConstant N ρ ε -
            9 * RegularityStructures.Phi43.hairerSunsetConstant N ρ ε))
        (𝓝[>] 0) (𝓝 κ) :=
  by exact RegularityStructures.Phi43.constantsComparison_limits

end RegularityStructures.Phi43

end
