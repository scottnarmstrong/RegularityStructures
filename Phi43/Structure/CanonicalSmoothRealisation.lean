/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothBasis
public import RegularityStructures.Abstract.Integration.Theorem512.Helpers

/-!+# Distributional realisation of the actual canonical lift

For smooth polynomially growing noise, the actual based canonical
functions define genuine semigroup distributions. Their compact-test
pairing is the ordinary integral, including the negative sector
[Hai14, Proposition 8.27, Remark 5.10]. No model bounds are arguments.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem globalPi_sum {κ : Kappa} (D : CanonicalData κ) (v : T) :
    D.globalPi v = fun z => ∑ τ : Symbol, v τ * D.globalPiBasis τ z := by
  rw [CanonicalData.globalPi, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rfl

open scoped ContDiff in
theorem canonicalGlobalPi_smooth (N : ℕ) {κ : Kappa} (noise : CanonicalNoise) (v : T) :
    ContDiff ℝ ∞ ((hairerCanonicalData (κ := κ) N noise).globalPi v) := by
  rw [globalPi_sum]
  exact ContDiff.sum fun τ _ =>
    contDiff_const.mul (canonicalGlobalPiBasis_smooth N noise τ)

open scoped ContDiff in
theorem canonicalPi_smooth (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (x : ParabolicSpace) (v : T) :
    ContDiff ℝ ∞ ((hairerCanonicalData (κ := κ) N noise).canonicalPi x v) := by
  rw [CanonicalData.canonicalPi_character_bridge, LinearMap.comp_apply]
  exact canonicalGlobalPi_smooth N noise _

end RegularityStructures.Phi43

end
