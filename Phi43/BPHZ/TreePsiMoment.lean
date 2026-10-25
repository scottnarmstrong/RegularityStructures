/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiField
public import Phi43.BPHZ.HairerCovarianceBounds
public import Phi43.Stochastic.ConstantsComparisonC2Bounds

/-!
# Joint measurability of the tree `Ψ`

For a regularised noise `ξ`, the field `(ω, z) ↦ Ψ(ω, z) = ∫ K(z - w) ξ ω w dw` is jointly
measurable (`measurable_hairerPsiField_uncurry`), since the integrand is jointly measurable in
`(ω, z, w)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The field `(ω, z) ↦ Ψ(ω, z)` is jointly measurable. -/
theorem measurable_hairerPsiField_uncurry {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    Measurable (fun q : Ω × SpaceTime => hairerPsiField N ξ q.1 q.2) := by
  have hjoint := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  have hK := measurable_constantsComparison_hairerKernelTorus N
  have hint : Measurable (fun q : (Ω × SpaceTime) × SpaceTime =>
      hairerKernelTorus N (q.1.2 - q.2) * ξ q.1.1 q.2) :=
    (hK.comp (measurable_snd.comp measurable_fst |>.sub measurable_snd)).mul
      (hjoint.comp (measurable_fst.fst.prodMk measurable_snd))
  exact hint.stronglyMeasurable.integral_prod_right'.measurable

end RegularityStructures.Phi43

end
