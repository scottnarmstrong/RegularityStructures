/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.Properties
public import RegularityStructures.Torus.HolderBesov

/-!
# Version selection for the stationary linear field

For a regularised noise, the joint measurable version of the forcing is supplied by item (W2) of
Lemma 4.1 of the statement.  Once the pathwise heat convolution has been identified with a
continuous-map-valued process `X`, the Holder--Besov Kolmogorov theorem gives the continuous
modification and its supremum moment bound. The theorem below keeps both interfaces in one
declaration: the convolution identification and its annealed increment estimates are hypotheses,
while the measurable forcing fact is proved directly from `IsRegularisedNoise`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures.Phi43

theorem toHolderBesov_lipschitzWith (η : NegExponent) :
    LipschitzWith (1 : ℝ≥0) (toHolderBesov η) := by
  intro f g
  rw [edist_dist, edist_dist]
  simp only [ENNReal.coe_one, one_mul]
  apply ENNReal.ofReal_le_ofReal
  rw [dist_eq_norm (toHolderBesov η f) (toHolderBesov η g),
    ← toHolderBesov_sub η f g, norm_toHolderBesov, dist_eq_norm f g]
  rw [← ENNReal.toReal_ofReal (norm_nonneg (f - g)), ofReal_norm]
  exact ENNReal.toReal_mono enorm_ne_top (holderBesovENorm_le η.2.le (f - g))

end RegularityStructures.Phi43

end
