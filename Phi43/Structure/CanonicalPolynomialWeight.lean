/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Growth
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Moderate polynomial weights for canonical-model reconstruction

The translation inequality for the actual parabolic size proves the
polynomial weight condition [Hos25, Definition 2.1, (2.1)–(2.2)] in main's
semigroup interface. No additional model premise is introduced.
-/

public section

namespace RegularityStructures.Phi43

/-- The polynomial envelopes proved for the canonical model are moderate
weights in the exact interface used by weighted reconstruction. -/
theorem canonicalPolynomialWeight_isModerate (p : ℕ) :
    parabolicSemigroup.IsModerateWeight (fun z => (1 + parabolicNorm z) ^ p) p where
  one_le z := one_le_pow₀ (by linarith [parabolicNorm_nonneg z])
  measurable := ((continuous_const.add continuous_parabolicNorm).pow p).measurable
  nonneg_exp := Nat.cast_nonneg _
  le y z := by
    rw [Real.rpow_natCast]
    exact (pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg z])
      (one_add_parabolicNorm_le z y) p).trans_eq (mul_pow _ _ _)

end RegularityStructures.Phi43

end
