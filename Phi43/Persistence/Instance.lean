/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedEnlargedModel
public import Phi43.Restart.Compat
public import Phi43.Restart.GrowthTranslate
public import Phi43.LiftBounds.Translate
public import RegularityStructures.Abstract.Translate.Realising
public import RegularityStructures.Abstract.Ext514W.IntExt

/-!
# The enlarged restarted model

`enlargedRestartModel N κ noise Cg q hg C s` is the time translate by `(s, 0)` of the enlarged
corrected smooth model `phi43EnlargedRenormalisedModel`.  It is compatible (`EnlargedCompat`) with
the time translate of the renormalised canonical model, is jointly measurable, and has a
qualitative growth model at the level `γ + α + α = κ` (these are the model hypotheses
`Phi43NearHyp.growth`, `.joint` of the restart composition).  The kernel-realising property on the
`Ξ`-free block is in `Phi43.Persistence.Realising`.
-/

public section

namespace RegularityStructures.Phi43.Persistence

/-- The enlarged restarted model: the time translate by `(s, 0)` of the enlarged corrected smooth
model. -/
@[expose] noncomputable def enlargedRestartModel (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (s : ℝ) :
    Model (phi43RegularityStructureF κ) parabolicSemigroup :=
  (phi43EnlargedRenormalisedModel N κ noise Cg q hg C).translate (LiftBounds.restartPoint s)

variable (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
  (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
  (C : RenormalisationConstants) (s : ℝ)

/-- The enlarged restarted model is compatible with the time translate of the renormalised
canonical model. -/
theorem enlargedRestartModel_compat :
    Restart.EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
      (LiftBounds.restartPoint s)) (enlargedRestartModel N κ noise Cg q hg C s) := by
  obtain ⟨h1, h2⟩ := phi43EnlargedRenormalisedModel_restrict_old N κ noise Cg q hg C
  refine ⟨fun x a t z => ?_, fun x y a => ?_⟩
  · exact h1 (x + LiftBounds.restartPoint s) a t (z + LiftBounds.restartPoint s)
  · simp only [enlargedRestartModel, Model.gammaMap_translate]
    exact h2 _ _ a

/-- The enlarged restarted model is jointly measurable. -/
theorem enlargedRestartModel_isJointMeasurable :
    (enlargedRestartModel N κ noise Cg q hg C s).IsJointMeasurable :=
  Model.isJointMeasurable_translate _ _
    (phi43EnlargedRenormalisedModel_isJointMeasurable N κ noise Cg q hg C)

/-- The enlarged restarted model has a qualitative growth model at every positive level
`γ' ≤ γ`. -/
theorem enlargedRestartModel_growth {γ' : ℝ} (hγ' : γ' ≤ gamma κ) (hpos : 0 < γ') :
    ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p' q' : ℝ),
      (enlargedRestartModel N κ noise Cg q hg C s).GrowthModel γ' C' C'' ρP ρG p' q' := by
  obtain ⟨C', C'', r, t, ρP, ρG, G⟩ := phi43EnlargedRenormalisedModel_growthModel N κ noise Cg q hg C
  exact ⟨C', C'', _, _, r, t, (G.mono_level hγ' hpos).translate _⟩

/-- The growth model at the level `γ + α + α = κ` used by the restart composition. -/
theorem enlargedRestartModel_growth_kappa :
    ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p' q' : ℝ),
      (enlargedRestartModel N κ noise Cg q hg C s).GrowthModel
        (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p' q' := by
  have hk : 0 < κ.1 := κ.2.1
  refine enlargedRestartModel_growth N κ noise Cg q hg C s ?_ ?_ <;>
    simp only [gamma, phi43Alpha] <;> linarith

end RegularityStructures.Phi43.Persistence

end
