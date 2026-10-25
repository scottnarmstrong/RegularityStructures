/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.DTaylorDeriv
public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# Linearity of the pairing in the test function and in the distribution

For the pairing `⟨Λ, φ⟩ = lim_{s ↓ 0} ∫ Λ_s φ` the limits exist for the test functions we use
(`tendsto_and_abs_pairing_word_scaledShell_le` etc.), and the slices `Λ_s φ` are integrable for
`s ∈ (0, 1]`.  This is enough to show

* `tendsto_integral_sub_sum_right`: `∫ Λ_s (φ₀ - ∑ c_i φ_i) → p₀ - ∑ c_i p_i`;
* `tendsto_integral_sub_sum_left`: `∫ (Λ₀ - ∑ c_i Λ_i)_s φ → p₀ - ∑ c_i p_i`;
* `integrable_mul_of_hasCompactSupport`: integrability of `Λ_s φ` for `φ` continuous with compact
  support and `Λ` of local order at some point.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

theorem hasCompactSupport_reflect {F : ParabolicSpace → ℝ} (hF : HasCompactSupport F)
    (c : ParabolicSpace) : HasCompactSupport fun w => F (c - w) :=
  hF.comp_homeomorph (Homeomorph.subLeft c)

end RegularityStructures

end
