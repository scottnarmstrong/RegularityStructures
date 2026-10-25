/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Realising.Def
public import Phi43.Structure.CanonicalKernelHairer
public import Phi43.Structure.CanonicalModel

/-!+# Polynomial admissibility of the actual smooth canonical model

The polynomial clause of Hairer [Hai14, Definition 5.9 / Assumption 5.3]
is an exact identity, not a bound assumption.
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- The actual canonical lift agrees with the polynomial sector pointwise. -/
theorem canonicalPi_polynomial (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (x : ParabolicSpace) (k : PolyIndex 2) :
    (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis (phi43PolyEmb k)) =
      polyEval x (Pi.single k 1) := by
  funext z
  rw [CanonicalData.canonicalPi_basis, polyEval_single]
  rcases polyIndex_two_cases k with hk | hk | hk | hk <;>
    simp [phi43PolyEmb, hk, CanonicalData.localPiBasis, CanonicalData.relCoord,
      evalParabolic, parabolicCoords, MvPolynomial.eval_monomial]

end RegularityStructures.Phi43

end
