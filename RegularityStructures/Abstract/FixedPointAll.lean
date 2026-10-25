/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointBanach
public import RegularityStructures.Abstract.FixedPointBounds
public import RegularityStructures.Abstract.FixedPointSlabSpace
public import RegularityStructures.Abstract.FixedPointSlabComplete
public import RegularityStructures.Abstract.FixedPointShortTime
public import RegularityStructures.Abstract.FixedPointTheorem
public import RegularityStructures.Abstract.FixedPointTruncation
public import RegularityStructures.Abstract.FixedPointTwoModels
public import RegularityStructures.Abstract.FixedPointPhi4
public import RegularityStructures.Abstract.FixedPointTimeSlab

/-!
# The abstract fixed-point theorem of [Hai14, §7]

Aggregator for the fixed-point layer:

* `FixedPointBanach`: the functional-analytic core of [Hai14, Theorem 7.8] in a Banach space,
  with the explicit existence time `fixedPointTime` and Lipschitz dependence on the data;
* `FixedPointBounds`: linearity and closedness of the bounds of `D^{γ,η}_P`;
* `FixedPointSlabSpace`, `FixedPointSlabComplete`: `D^{γ,η}_P(V)` on a time slab as a Banach
  space (`Model.SlabSpace`);
* `FixedPointShortTime`: the short-time gain `T^{κ/𝔰₀}` ([Hai14, Theorem 7.1 (proof), Lemma 7.3]);
* `FixedPointTheorem`: [Hai14, Theorem 7.8] for a fixed model on the slab;
* `FixedPointTruncation`: `Q_{<γ}` on `D^{γ',η'}_P` and Theorem 7.8 with Hairer's exponent
  conditions `γ ≤ γ̄ + β`, `η < (η̄ ∧ ζ̄) + β`;
* `FixedPointTwoModels`: Lipschitz dependence on the model;
* `FixedPointConsistency`: restriction to shorter slabs, local-in-time uniqueness;
* `FixedPointUniqueness`: uniqueness among all solutions on the slab, under the gain on late
  slabs (the continuity argument of [Hai14, Theorem 7.8]);
* `FixedPointPhi4`: the Φ⁴₃ nonlinearity `U ↦ U³` and [Hai14, Proposition 9.8] (local part) with an
  abstract integration operator; `FixedPointPhi4Integration`: the same with the integration
  operator given through the bounds of [Hai14, Theorem 7.1];
* `FixedPointTimeSlab`: the concrete slabs `(0, T] × ℝ³` and the distance `|t|^{1/2}` to
  `{t = 0}` in parabolic space-time, discharging the slab hypotheses with `𝔰₀ = 2`;
  `FixedPointPhi4TimeSlab`: Proposition 9.8 (local part) and whole-slab uniqueness there;
* `FixedPointMaximal`: maximal solutions and the blow-up alternative from local existence,
  local uniqueness and the restart property ([Hai14, Proposition 7.11] and after).

Source: [Hai14] = arXiv:1303.5113v4, §7.
-/
