/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Series

/-!
# Assembly of a smooth modification into a regularised noise

The general smooth-modification theorem is independent of the mollifier.  This short assembly lemma
records exactly how its output specializes to `IsRegularisedNoise`; the smoothness and time-support
hypotheses are explicit so that the periodisation argument can discharge them independently.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem regularisedNoise_exists_of_smoothVersion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (rho : ℝ × (Fin 3 → ℝ) → ℝ) (eps : ℝ)
    (_hPhi : IsSmoothOnSpaceTime (periodise rho eps))
    (_hR : ∃ R : ℝ, ∀ z : SpaceTime, R < |z.1| → periodise rho eps z = 0)
    (hversion : ∃ xi : Ω → SpaceTime → ℝ,
      (∀ w, IsSmoothOnSpaceTime (xi w)) ∧
        ∀ z, Measurable (fun w => xi w z) ∧
          (fun w => xi w z) =ᵐ[P] W (fun w => periodise rho eps (z - w))) :
    ∃ xi, IsRegularisedNoise P W rho eps xi := by
  rcases hversion with ⟨xi, hxi_smooth, hxi_eval⟩
  refine ⟨xi, hxi_smooth, ?_⟩
  intro z
  refine ⟨(hxi_eval z).1, (hxi_eval z).2.trans ?_⟩
  rfl

end RegularityStructures.Phi43

end
