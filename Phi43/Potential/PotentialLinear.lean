/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.IsMassivePotential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Linearity of the massive potential

If `ψ₁, ψ₂` are the massive potentials of `f₁, f₂`, then `c • (ψ₁ - ψ₂)` is the massive potential of
`c (f₁ - f₂)` (`isMassivePotential_sub_smul`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Potential

open RegularityStructures

theorem isMassivePotential_sub_smul {f₁ f₂ : SpaceTime → ℝ} {ψ₁ ψ₂ : ℝ → C(Torus3, ℝ)}
    (h₁ : IsMassivePotential f₁ ψ₁) (h₂ : IsMassivePotential f₂ ψ₂)
    (c : ℝ) :
    IsMassivePotential (fun w => c * (f₁ w - f₂ w)) (fun t => c • (ψ₁ t - ψ₂ t)) := by
  refine ⟨fun t x => ?_, fun t x => ?_⟩
  · have := (((h₁.1 t x).sub (h₂.1 t x)).const_mul c)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.sub_apply]
    ring
  · have e : ∀ w : SpaceTime, massiveHeatKernel (((t, x) : SpaceTime) - w) * (c * (f₁ w - f₂ w)) =
        c * (massiveHeatKernel (((t, x) : SpaceTime) - w) * f₁ w -
          massiveHeatKernel (((t, x) : SpaceTime) - w) * f₂ w) := fun w => by ring
    simp only [e]
    rw [integral_const_mul, integral_sub (h₁.1 t x) (h₂.1 t x)]
    simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul]
    rw [h₁.2 t x, h₂.2 t x]

end RegularityStructures.Potential

end
