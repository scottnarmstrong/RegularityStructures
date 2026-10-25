/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalModel

/-!
# Literal diagonal evaluation for the smooth canonical lift

Hairer [Hai14, Remark 3.15]. The diagonal below is defined by its actual
evaluation formula, not by a bundle of reconstruction claims. Canonical
covariance gives the exact algebraic reconstruction remainder.
-/

public noncomputable section

namespace RegularityStructures.Phi43

private theorem coord_symm_single (τ : Symbol) :
    phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
  apply phi43CoordinateEquiv.injective
  simp [phi43CoordinateEquiv_basis]

/-- Actual evaluation on a coordinate vector is the finite tree expansion. -/
theorem canonicalPi_coord_sum {κ : Kappa} (D : CanonicalData κ)
    (x y : ParabolicSpace) (a : Symbol → ℝ) :
    D.canonicalPi x (phi43CoordinateEquiv.symm a) y =
      ∑ τ : Symbol, a τ * D.canonicalPi x (basis τ) y := by
  conv_lhs => rw [eq_sum_single a]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, coord_symm_single]

end RegularityStructures.Phi43

end
