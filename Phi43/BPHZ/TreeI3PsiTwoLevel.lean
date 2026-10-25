/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiSlab

/-!
# Two-level domination of a double integral

If `|F w w'| ≤ G w w'` where, for almost every `w`, `G w` is integrable with `∫ G w ≤ H w` and `H`
is integrable, then `F` is integrable on the product and the iterated integral of `F` is at most
`∫ H` in absolute value.  This is the integrability statement for the Wick-diagram integrands
(Fubini for the pairing `∫∫ δK δK Q ⋯`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem integrable_prod_of_two_level {F G : SpaceTime → SpaceTime → ℝ} {H : SpaceTime → ℝ}
    (hF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume))
    (hG : ∀ᵐ w : SpaceTime ∂volume, Integrable (G w))
    (hGH : ∀ᵐ w : SpaceTime ∂volume, ∫ v, G w v ≤ H w) (hH : Integrable H)
    (hFG : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤ G w v) :
    Integrable (Function.uncurry F) (volume.prod volume) ∧
      |∫ w, ∫ v, F w v| ≤ ∫ w, H w := by
  have hnormle : ∀ᵐ w : SpaceTime ∂volume, ∫ v, ‖F w v‖ ≤ H w := by
    filter_upwards [hG, hGH, hFG] with w h1 h2 h3
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) h1
      ?_).trans h2
    filter_upwards [h3] with v hv
    rwa [Real.norm_eq_abs]
  have hint : Integrable (fun w => ∫ v, ‖F w v‖) := by
    refine Integrable.mono' hH hF.norm.integral_prod_right' ?_
    filter_upwards [hnormle] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
    exact hw
  refine ⟨(integrable_prod_iff hF).2 ⟨?_, hint⟩, ?_⟩
  · filter_upwards [hG, hFG, hF.prodMk_left] with w h1 h2 h3
    refine Integrable.mono' h1 h3 ?_
    filter_upwards [h2] with v hv
    rwa [Real.norm_eq_abs]
  · calc |∫ w, ∫ v, F w v| = ‖∫ w, ∫ v, F w v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ w, ‖∫ v, F w v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w, ∫ v, ‖F w v‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
          hint (Filter.Eventually.of_forall fun w => norm_integral_le_integral_norm _)
      _ ≤ ∫ w, H w :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
          integral_nonneg fun v => norm_nonneg _) hH hnormle

end RegularityStructures

end
