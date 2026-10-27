/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

import GlobalPhi43.Flow.CanonicalReferenceFlow
import GlobalPhi43.Flow.ReferenceGlobalFlow
import GlobalPhi43.Proofs.GlobalDynamicsProfile
public import GlobalPhi43Statements.Defs.IsGlobalPhi43Flow

public noncomputable section
namespace GlobalPhi43
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open Attachment
open scoped NNReal

universe u

/-- Global stochastic dynamics with a profile fixed before the source space.
One reference flow and one law satisfy all eight global-flow properties. -/
theorem globalDynamics :
    ∀ (a : ℝ) (η : NegExponent) (_hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))),
    ∃ K : ℝ → ℝ≥0,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W),
    ∃ (Ω₀ : Set Ω) (v : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (μ : Measure (HolderBesov η)),
      IsGlobalPhi43Flow K P W a η Ω₀ v μ := by
  intro a η hη
  refine ⟨globalDynamicsProfile.{u} a η, ?_⟩
  intro Ω _ P _ _ W hW
  obtain ⟨v⟩ := Flow.exists_canonical_referenceFlow a η hη P W hW
  obtain ⟨μ, hglobal, _⟩ := Flow.referenceEventFlow_global P W hW
    referencePhi0 referencePhi0_isMollifier a η hη
    (referenceNoiseFamily P W hW) (fun _ hε => referenceNoiseFamily_spec P W hW hε) v
  exact ⟨_, (fun t s x ω => v.value ω t s x), (μ : Measure _), hglobal⟩

end GlobalPhi43
