/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiMoment

/-!
# Measurability of the mollified kernel

The mollified Hairer kernel `K_ε = hairerMollifiedKernel N ρ ε`, `K_ε(z) = ∫ K(z - w) ρ_ε^♯(w) dw`,
is measurable (`measurable_hairerMollifiedKernel`). It enters the covariance of the difference
`Ψ_ε - Ψ_ε'` of two scales of the tree `Ψ`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- The mollified Hairer kernel is measurable. -/
theorem measurable_hairerMollifiedKernel (N : ℕ) (hρ : IsMollifier ρ) (ε : ℝ) :
    Measurable (hairerMollifiedKernel N ρ ε) := by
  have hint : Measurable (fun q : SpaceTime × SpaceTime =>
      hairerKernelTorus N (q.1 - q.2) * periodise ρ ε q.2) :=
    ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_fst.sub measurable_snd)).mul ((measurable_periodise ρ hρ).comp measurable_snd)
  exact hint.stronglyMeasurable.integral_prod_right'.measurable

end RegularityStructures.Phi43

end
