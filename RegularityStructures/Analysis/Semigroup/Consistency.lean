/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Conservative kernels: functions are faithfully represented

A regularising semigroup is *conservative* if `∫ Q_t(x, y) dy = 1` for `t > 0`
([Hos25, Definition 2.6 (ii)], arXiv:2310.07396v2). For such a semigroup:

* `tendsto_apply_nhdsGT`: `Q_s g (x) → g (x)` as `s ↓ 0` for a bounded measurable `g` continuous
  at `x` with respect to `scaleDist` (approximate identity);
* `pairing_ofFunction`: the pairing of the `Q`-distribution `ofFunction g` of a bounded
  measurable, everywhere continuous `g` with an integrable `φ` is `∫ g φ dμ`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- The kernel is conservative: `∫ Q_t(x, y) dμ(y) = 1` for `t > 0`
([Hos25, Definition 2.6 (ii)]). -/
def IsConservative : Prop := ∀ ⦃t : ℝ⦄, 0 < t → ∀ x, ∫ y, K.kernel t x y ∂μ = 1

end RegularityStructures.RegularisingSemigroup

end

