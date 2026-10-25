/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestDouble

/-!
# Covariance-weighted double integrals for a semigroup test profile

Let `g` be a semigroup test profile at scale `lam ∈ (0, 1]` and base point `x`
(`SemigroupTestProfile`), and `Φ(u, v)` a "covariance" on space-time pairs which satisfies

* the local pair bound `|Φ(u, v)| ≤ B s(u - x)^ζ s(u - v)^e` when `s(u - x), s(v - x) ≤ 1`, and
* polynomial growth `|Φ(u, v)| ≤ B (1 + s(u - x) + s(v - x))^m` otherwise.

Then `∫∫ |g u| |g v| |Φ(u, v)| ≤ C B lam^(ζ+e)`
(`SemigroupTestProfile.integral_double_abs_cov_le`).  Time is unbounded, so the polynomial growth is
absorbed by the moments of `g`: outside the unit ball one of the two sizes exceeds `1`, and
`(1 + a + b)^m ≤ 3^m (a^n + b^n)` for `n ≥ m` and `max a b ≥ 1`, with
`∫∫ |g u| |g v| s(u - x)^n ≤ Mom n Mom 0 lam^n ≤ Mom n Mom 0 lam^(ζ+e)` for `lam ≤ 1`, `n ≥ ζ + e`.
The pointwise hypotheses are only required where `s(u - x) > 0` and `s(u - v) > 0`, which holds
almost everywhere.
-/

public section

open MeasureTheory

namespace RegularityStructures

namespace SemigroupTestProfile

variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

/-- Almost everywhere on pairs, both sizes are positive. -/
theorem ae_pos_pair (x : SpaceTime) :
    ∀ᵐ w : SpaceTime × SpaceTime ∂volume,
      0 < torusParabolicSize (w.1 - x) ∧ 0 < torusParabolicSize (w.1 - w.2) := by
  have hmeas : MeasurableSet {w : SpaceTime × SpaceTime |
      0 < torusParabolicSize (w.1 - x) ∧ 0 < torusParabolicSize (w.1 - w.2)} :=
    (measurableSet_lt measurable_const (Phi43.measurable_torusParabolicSize.comp
      (measurable_fst.sub measurable_const))).inter
      (measurableSet_lt measurable_const (Phi43.measurable_torusParabolicSize.comp
        (measurable_fst.sub measurable_snd)))
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
  filter_upwards [ae_pos_torusParabolicSize_sub_right x] with u hu
  filter_upwards [treePsi_ae_pos_size_sub u] with v hv
  exact ⟨hu, hv⟩

end SemigroupTestProfile

end RegularityStructures

end
