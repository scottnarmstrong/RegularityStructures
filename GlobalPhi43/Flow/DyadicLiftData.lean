module

public import GlobalPhi43.Flow.ReferencePotential
public import GlobalPhi43.Flow.LocalConsistency

@[expose] public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Reindex the specified n>=1 sequence by Nat without assuming growth at index zero. -/
def dyadicTailScale (n : ℕ) : ℝ := (2⁻¹ : ℝ) ^ (n + 1)

theorem dyadicTailScale_eq (n : ℕ) : dyadicTailScale n = ((2 : ℝ) ^ (n + 1))⁻¹ := by
  simp only [dyadicTailScale, inv_pow]

/-- The corrected common event for the single concrete reference model/potential family. -/
def referenceEvent {Ω : Type*} (N : ℕ) (κ : Kappa) (ρ : ParabolicSpace → ℝ) (a α : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω)) : Set Ω :=
  commonEvent N ρ a α ξ (referenceAttachedModel N κ ρ a ξ hsmooth) (referencePotential ξ hsmooth)

/-- Actual LiftData on the fixed event, for the same concrete dyadic tail at every horizon. -/
def dyadicLiftData {Ω : Type*} (N : ℕ) (κ : Kappa) (ρ : ParabolicSpace → ℝ) (a α : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ω : Ω) (hω : ω ∈ referenceEvent N κ ρ a α ξ hsmooth) (n : ℕ) : LiftData N κ where
  forcing := ξ (dyadicTailScale n) ω
  constants := (wickConstant ρ (dyadicTailScale n) + a / 3, sunsetConstant ρ (dyadicTailScale n) + 0)
  model := referenceAttachedModel N κ ρ a ξ hsmooth (dyadicTailScale n) ω
  potential := referencePotential ξ hsmooth (dyadicTailScale n) ω
  moderate := commonEvent_lift N ρ a α ξ _ _ hω (n + 1) (by omega)

/-- A probability-one event, with no supplied potential, moment, lift, or event premise. -/
theorem referenceEvent_measurable_measure_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
    (α : NegExponent) (hα : (α : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκα : κ.1 < -(1 / 2 : ℝ) - α)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) :
    MeasurableSet (referenceEvent N κ ρ a α ξ (fun ε hε => (hξ ε hε).1)) ∧
      P (referenceEvent N κ ρ a α ξ (fun ε hε => (hξ ε hε).1)) = 1 := by
  exact (referenceAttachedModel_events P W hW N κ ρ hρ a ξ hξ
    (referencePotential ξ (fun ε hε => (hξ ε hε).1))
    (fun ε hε => referencePotential_ae P W hW ρ hρ ξ hξ hε) hκE hN α hα hκα).2.2

end GlobalPhi43.Flow
