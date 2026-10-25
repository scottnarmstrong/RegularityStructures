/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsL1
public import RegularityStructures.Analysis.Parabolic.TestFunction

/-!
# First parabolic moment of the rescaled mollifier

`∫ |ρ_ε(y)| ‖y‖_par dy = ε ∫ |ρ(y)| ‖y‖_par dy`, from the homogeneity of the parabolic norm and
the change of variables `y ↦ ε y`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem hasCompactSupport_rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : 0 < ε) : HasCompactSupport (rescale ρ ε) := by
  let a : ℝ := ε ^ (-2 : ℤ)
  let b : ℝ := ε⁻¹
  let e : (ℝ × (Fin 3 → ℝ)) ≃ₜ (ℝ × (Fin 3 → ℝ)) :=
    Homeomorph.prodCongr (Homeomorph.mulRight₀ a (by
      dsimp [a]
      exact zpow_ne_zero _ (ne_of_gt hε)))
      (Homeomorph.smulOfNeZero b (by
        dsimp [b]
        exact inv_ne_zero (ne_of_gt hε)))
  have he := hρ.hasCompactSupport.comp_homeomorph e
  have hm := he.mul_left (f := fun _ : ℝ × (Fin 3 → ℝ) => ε ^ (-5 : ℤ))
  convert hm using 1
  funext q
  simp [e, a, b, rescale, Function.comp_def, zpow_neg, Prod.map, ne_of_gt hε]
  ring_nf

end RegularityStructures.Phi43

end
