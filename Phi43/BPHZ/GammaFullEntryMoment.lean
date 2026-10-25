/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullParamMoment
public import Phi43.BPHZ.GammaFullDet
import Mathlib.Tactic

/-!
# The random `Γ`-entries of the canonical model at the cutoff `γ = 1 + 3κ`

For the nine random symbols `i` (`IsGammaFullRandom`) and every `j ≠ i`, with
`P ω = gammaFullParam N κ C (ξ ω) y x`, the entries `structureGroupMap (P ω) (basis i) j` have
moments `∫⁻ ‖·‖ₑ^q ≤ ofReal (C₀ d^(deg i - deg j + κ̄))^q` for all `x, y : ParabolicSpace`, once
the parameters of `P` have moments at their own exponents. This module proves the two elementary
steps of that case analysis: a vanishing entry has vanishing moment
(`lintegral_enorm_pow_of_eq_zero`), and an entry equal to a parameter whose exponent matches the
degree gap inherits its bound (`gammaFull_bound_of_param`). The case analysis itself is
`gammaShift_entry_lintegral_le`. The degree gaps of the nonzero entries are:

| entry                      | gap          | parameter bound used             |
|----------------------------|--------------|----------------------------------|
| `I(Ψ²) → 1`                | `1 - 2κ`     | `c₂`: `1 - 2κ + κ̄`               |
| `I(Ψ³) → 1`                | `1/2 - 3κ`   | `c₃`: `1/2 - 3κ + κ̄`             |
| `I(Ψ)Ψ → Ψ`, `I(Ψ)Ψ² → Ψ²` | `3/2 - κ`    | `c₁`: `3/2 - κ + κ̄`              |
| `I(Ψ)Ψ → ΨXₖ`, `I(Ψ)Ψ² → Ψ²Xₖ` | `1/2 - κ` | `gₖ`: `1/2 - κ + κ̄`            |
| `I(Ψ²)Ψ → Ψ`, `I(Ψ²)Ψ² → Ψ²` | `1 - 2κ`  | `c₂`                             |
| `I(Ψ³)Ψ → Ψ`, `I(Ψ³)Ψ² → Ψ²` | `1/2 - 3κ` | `c₃`                            |
| `I(Ψ³)² → I(Ψ³)`          | `1/2 - 3κ`   | `2 c₃`                           |
| `I(Ψ³)² → 1`               | `1 - 6κ`     | `c₃²` (`2q`-th moment of `v₃`)   |

so the gaps add up with the parameter exponents (`gap + κ̄` in all cases).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem lintegral_enorm_pow_of_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} {q : ℕ} (hq : 1 ≤ q) (hf : ∀ ω, f ω = 0) (b : ENNReal) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ b := by
  have : ∀ ω, ‖f ω‖ₑ ^ q = 0 := fun ω => by
    rw [hf ω]; simp; omega
  simp [this]

/-- Bound for an entry equal to a parameter whose exponent matches the gap. -/
theorem gammaFull_bound_of_param {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    {q : ℕ} {a C₀ d E e : ℝ} (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (a * d ^ E) ^ q)
    (ha : a ≤ C₀) (hd : 0 ≤ d) (hE : E = e) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (C₀ * d ^ e) ^ q := by
  subst hE
  exact le_ofReal_pow_mono h (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hd _))

end RegularityStructures.Phi43

end
