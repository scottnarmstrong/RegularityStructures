/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullEntryMoment
public import Phi43.BPHZ.GammaFullParamMomentSub
import Mathlib.Tactic

/-!
# The two-model differences of the random `Γ`-entries at the cutoff `γ = 1 + 3κ`

For two canonical models with parameters `P ω = gammaFullParam N κ C (ξ ω) y x` and
`P' ω = gammaFullParam N κ C' (ξ' ω) y x`, an entry difference equal to a parameter difference
whose exponent matches the degree gap inherits its bound
`∫⁻ ‖Γ_{yx} e_i (j) - Γ'_{yx} e_i (j)‖ₑ^q ≤ ofReal (C₀ (ε ∨ ε')^θ d^(deg i - deg j + κ̄))^q`
(`gammaFull_bound_of_param_sub`). For the entry of `I(Ψ³)²` at `1` one uses
`c₃² - c₃'² = (c₃ - c₃')(c₃ + c₃')`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem gammaFull_bound_of_param_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} {q : ℕ} {a C₀ M d E e : ℝ}
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (a * M * d ^ E) ^ q)
    (ha : a ≤ C₀) (hM : 0 ≤ M) (hd : 0 ≤ d) (hE : E = e) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (C₀ * M * d ^ e) ^ q := by
  subst hE
  exact le_ofReal_pow_mono h (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ha hM) (Real.rpow_nonneg hd _))

end RegularityStructures.Phi43

end
