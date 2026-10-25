/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.StepConsts
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist

/-!
# Elementary estimates for the local Lipschitz step

The noise parts of the size `phi43Size` and of the distance `phi43Dist` control the massive
potentials on `[-1, T + 1]` (`holderBesovENorm_le_of_phi43Size_le`,
`holderBesovENorm_sub_le_of_phi43Dist_le`); the `η`-norm
of a difference obeys the triangle inequality (`holderBesovENorm_sub_le_add`); and the final
arithmetic of the step (`step_arith`).
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.LocalLipschitz

variable {κ : Kappa} {η T : ℝ} {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup}
  {ψ ψ' : ℝ → C(Torus3, ℝ)}

theorem holderBesovENorm_le_of_phi43Size_le {B : ℝ}
    (h : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B) {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) (T + 1)) :
    holderBesovENorm η (ψ r) ≤ ENNReal.ofReal B := by
  refine le_trans ?_ (le_add_self.trans h)
  exact le_iSup₂ (f := fun t (_ : t ∈ Icc (-1 : ℝ) (T + 1)) => holderBesovENorm η (ψ t)) r hr

theorem holderBesovENorm_sub_le_of_phi43Dist_le {δ : ℝ}
    (h : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ) {r : ℝ}
    (hr : r ∈ Icc (-1 : ℝ) (T + 1)) :
    holderBesovENorm η (ψ r - ψ' r) ≤ ENNReal.ofReal δ := by
  refine le_trans ?_ (le_add_self.trans h)
  exact le_iSup₂ (f := fun t (_ : t ∈ Icc (-1 : ℝ) (T + 1)) => holderBesovENorm η (ψ t - ψ' t))
    r hr

theorem holderBesovENorm_sub_le_add (η : ℝ) (f g : C(Torus3, ℝ)) :
    holderBesovENorm η (f - g) ≤ holderBesovENorm η f + holderBesovENorm η g := by
  rw [sub_eq_add_neg]
  exact (holderBesovENorm_add_le η f (-g)).trans_eq (by rw [holderBesovENorm_neg])

/-- The final arithmetic of the step. -/
theorem step_arith {x δ K' DY : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) (hK' : 0 ≤ K') (hDY : 0 ≤ DY) :
    x + 4 * δ + K' * (x + δ * DY + 2 * δ + δ) ≤ (1 + K') * (8 + DY) * (x + δ) := by
  nlinarith [mul_nonneg hK' hx, mul_nonneg hK' hδ, mul_nonneg (mul_nonneg hK' hDY) hx,
    mul_nonneg (mul_nonneg hK' hDY) hδ, mul_nonneg hDY hx, mul_nonneg hDY hδ]

end RegularityStructures.Phi43.LocalLipschitz

end
