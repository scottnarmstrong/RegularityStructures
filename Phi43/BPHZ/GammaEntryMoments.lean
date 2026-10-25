/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentUniformLp
public import Phi43.BPHZ.PositiveMomentGammaMoment
import Mathlib.Tactic

/-!
# Combining near and far moment bounds

The moment bounds for the random `Γ`-entries are first proved for `d = d(y, x) ≤ 1` only. The
Kolmogorov bound for the model norms needs them for all pairs `x, y : ParabolicSpace`.
`moment_near_far_bound` combines a bound valid for `d ≤ 1` with a uniform bound
`∫⁻ ‖f‖ₑ^q ≤ ofReal C ^ q` (for instance those of `Phi43.BPHZ.GammaMomentUniformLp`), using
`d^e ≥ 1` for `d ≥ 1`, into a bound for all `d` with a constant independent of `d`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Combination of a bound valid for `d ≤ 1` with a uniform bound, for `d^e ≥ 1` when `d ≥ 1`. -/
theorem moment_near_far_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    {q : ℕ} {Cn Cf a d e : ℝ} (hCf : 0 ≤ Cf) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hd : 0 ≤ d) (hnear : d ≤ 1 → ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (Cn * a * d ^ e) ^ q)
    (hfar : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (Cf * a) ^ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (max Cn Cf * a * d ^ e) ^ q := by
  have hde : 0 ≤ d ^ e := Real.rpow_nonneg hd _
  by_cases h1 : d ≤ 1
  · refine (hnear h1).trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) ha) hde
  · have h1' : 1 ≤ d := (lt_of_not_ge h1).le
    have hge : 1 ≤ d ^ e := Real.one_le_rpow h1' he
    refine hfar.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
    calc Cf * a = Cf * a * 1 := (mul_one _).symm
      _ ≤ max Cn Cf * a * d ^ e := by
        have h2 : Cf * a ≤ max Cn Cf * a := mul_le_mul_of_nonneg_right (le_max_right _ _) ha
        have h3 : 0 ≤ Cf * a := mul_nonneg hCf ha
        calc Cf * a * 1 ≤ max Cn Cf * a * 1 := by linarith
          _ ≤ max Cn Cf * a * d ^ e :=
            mul_le_mul_of_nonneg_left hge (le_trans h3 h2)

end RegularityStructures.Phi43

end
