/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion
public import Phi43.RegularisedNoise.Properties
public import Phi43.RegularisedNoise.SmoothModification

/-!
# Existence and uniqueness of the regularised noise

This assembles item (W2) of Lemma 4.1 of the statement once a smooth version of the translated
kernel is available.  The two analytic periodisation obligations are explicit, so the module remains
independent of the locally finite spatial periodisation proof.  The resulting conjunction
(`regularisedNoise_exists_unique_of_smoothVersion`) is item (W2) with the existence of the smooth
version as the only remaining input.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem regularisedNoise_exists_unique_of_smoothVersion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W)
    (rho : ℝ × (Fin 3 → ℝ) → ℝ) (eps : ℝ)
    (hPhi : IsSmoothOnSpaceTime (periodise rho eps))
    (hR : ∃ R : ℝ, ∀ z : SpaceTime, R < |z.1| → periodise rho eps z = 0)
    (hversion : ∃ xi : Ω → SpaceTime → ℝ,
      (∀ w, IsSmoothOnSpaceTime (xi w)) ∧
        ∀ z, Measurable (fun w => xi w z) ∧
          (fun w => xi w z) =ᵐ[P] W (fun w => periodise rho eps (z - w))) :
    (∃ xi, IsRegularisedNoise P W rho eps xi) ∧
      (∀ xi xi', IsRegularisedNoise P W rho eps xi →
        IsRegularisedNoise P W rho eps xi' → ∀ᵐ ω ∂P, xi ω = xi' ω) ∧
      ∀ xi, IsRegularisedNoise P W rho eps xi →
        Measurable (fun p : Ω × SpaceTime => xi p.1 p.2) := by
  refine ⟨regularisedNoise_exists_of_smoothVersion P W rho eps hPhi hR hversion, ?_, ?_⟩
  · intro xi xi' hxi hxi'
    exact regularisedNoise_indistinguishable P W rho eps xi xi' hxi hxi'
  · intro xi hxi
    exact regularisedNoise_measurable_uncurry P W rho eps xi hxi

end RegularityStructures.Phi43

end
