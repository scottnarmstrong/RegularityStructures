/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Basic
public import RegularityStructures.Analysis.Semigroup.Pairing.Moment

/-!
# Kernel moments against a distribution of local order with growth

`LocalBall.of_growth`: a `Q`-distribution of local order `γ` with polynomial growth `q ≥ 0`
(`IsLocalOrderGrowth`) satisfies the `LocalBall` hypotheses on every ball of radius `lam ≥ 0`
with constant `C (1 + lam)^q`. The kernel-moment bound uses
`(1 + d(z, x₀))^q d(z, x₀)^r ≤ 2^{q+r} ((1 + lam)^{q+r} + d(z, y)^{q+r})` for `d(y, x₀) ≤ lam`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

theorem rpow_mul_rpow_le {D w b q r : ℝ} (hD : 0 ≤ D) (hw : 0 ≤ w) (hb : 1 ≤ b) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hDw : D ≤ w + b - 1) :
    (1 + D) ^ q * D ^ r ≤ 2 ^ (q + r) * (b ^ (q + r) + w ^ (q + r)) := by
  have h1 : 1 + D ≤ b + w := by linarith
  have h2 : D ≤ b + w := by linarith
  have hbw : 0 < b + w := by linarith
  calc (1 + D) ^ q * D ^ r ≤ (b + w) ^ q * (b + w) ^ r :=
        mul_le_mul (Real.rpow_le_rpow (by linarith) h1 hq) (Real.rpow_le_rpow hD h2 hr)
          (Real.rpow_nonneg hD _) (Real.rpow_nonneg hbw.le _)
    _ = (b + w) ^ (q + r) := (Real.rpow_add hbw _ _).symm
    _ ≤ _ := rpow_add_le_mul (by linarith) hw (by linarith)

end RegularityStructures.RegularisingSemigroup

end
