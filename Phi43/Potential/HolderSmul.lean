/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.HolderContraction

/-!
# Homogeneity of the `𝒞^η` norm

`holderBesovENorm η (c • g) = ofReal |c| * holderBesovENorm η g`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Potential

open RegularityStructures

theorem heatSemigroup_smul' {u : ℝ} (hu : 0 < u) (c : ℝ) (g : C(Torus3, ℝ)) (x : Torus3) :
    heatSemigroup u (c • g) x = c * heatSemigroup u g x := by
  rw [← PDE.heatOp_eq_heatSemigroup hu, PDE.heatOp_smul, ← PDE.heatOp_eq_heatSemigroup hu]
  rfl

theorem holderBesovENorm_smul (η c : ℝ) (g : C(Torus3, ℝ)) :
    holderBesovENorm η (c • g) = ENNReal.ofReal |c| * holderBesovENorm η g := by
  have h : ∀ u ∈ Ioc (0 : ℝ) 1, ⨆ x, ‖heatSemigroup u (c • g) x‖ₑ =
      ENNReal.ofReal |c| * ⨆ x, ‖heatSemigroup u g x‖ₑ := by
    intro u hu
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun x => ?_
    rw [heatSemigroup_smul' hu.1, enorm_mul, ← ofReal_norm, Real.norm_eq_abs]
  calc holderBesovENorm η (c • g)
      = ⨆ u : ℝ, ⨆ (_ : u ∈ Ioc (0 : ℝ) 1), ENNReal.ofReal |c| *
          (ENNReal.ofReal (u ^ (-η / 2)) * ⨆ x, ‖heatSemigroup u g x‖ₑ) := by
        unfold holderBesovENorm
        refine iSup_congr fun u => iSup_congr fun hu => ?_
        rw [h u hu]
        ring
    _ = ENNReal.ofReal |c| * holderBesovENorm η g := by
        unfold holderBesovENorm
        simp only [ENNReal.mul_iSup]

end RegularityStructures.Potential

end
