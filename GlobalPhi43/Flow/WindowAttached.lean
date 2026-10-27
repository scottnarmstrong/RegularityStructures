module

public import GlobalPhi43.Flow.CommonEvent

@[expose] public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- Part-2 representatives for the reference regularisations. On (0,1] this uses precisely
attachedModel, including its exact growth event and zero-noise fallback. -/
def referenceAttachedModel {Ω : Type*} (N : ℕ) (κ : Kappa)
    (ρ : ParabolicSpace → ℝ) (a : ℝ) (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ε : ℝ) (ω : Ω) : Model (phi43RegularityStructure κ) parabolicSemigroup := by
  classical
  exact if hε : ε ∈ Ioc (0 : ℝ) 1 then
    Attachment.attachedModel N κ (ξ ε) (wickConstant ρ ε + a / 3, sunsetConstant ρ ε + 0)
      (hsmooth ε hε) ω
  else Attachment.moderateModel N κ (fun _ => 0)
    (wickConstant ρ ε + a / 3, sunsetConstant ρ ε + 0) contDiff_const hasPhi43NoiseGrowth_zero

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (N : ℕ) (κ : Kappa) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
  (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ))
  (hψ : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, IsMassivePotential (ξ ε ω) (ψ ε ω))

include W hW hρ hψ

/-- No stochastic estimate is assumed for the attached models: the literal lift premise follows
from the actual growth theorem, attachedModel_spec and the source massive-potential premise. -/
theorem referenceAttachedModel_lift_ae {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Statements.IsModeratePhi43Lift N κ (ξ ε ω)
      (wickConstant ρ ε + a / 3, sunsetConstant ρ ε + 0)
      (referenceAttachedModel N κ ρ a ξ (fun ε hε => (hξ ε hε).1) ε ω) (ψ ε ω) := by
  classical
  have hg := (Attachment.growthEvent_measurable_measure_one P W hW ρ hρ hε (ξ ε) (hξ ε hε))
  have hae : ∀ᵐ ω ∂P, ω ∈ Attachment.growthEvent (ξ ε) :=
    (mem_ae_iff_prob_eq_one hg.1).mpr hg.2
  filter_upwards [hae, hψ ε hε] with ω hω hpot
  refine ⟨hω, ?_, hpot⟩
  simp only [referenceAttachedModel, dite_eq_left hε]
  exact Attachment.attachedModel_spec N κ (ξ ε) _ (hξ ε hε).1 ω hω

/-- The actual Part-2 family has the literal full window event, compact-window dyadic Cauchy
property and exact common event. No moment, shift rate or common-event premise is supplied. -/
theorem referenceAttachedModel_events [P.IsComplete]
    (hκE : κ.1 ∉ Statements.excludedKappa) (hN : 5 ≤ N)
    (α : NegExponent) (hα : (α : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκα : κ.1 < -(1 / 2 : ℝ) - α) :
    let Z := referenceAttachedModel N κ ρ a ξ (fun ε hε => (hξ ε hε).1)
    (MeasurableSet (windowEvent (lossExponent κ) Z ψ) ∧
      P (windowEvent (lossExponent κ) Z ψ) = 1) ∧
    (MeasurableSet (windowCauchyEvent (lossExponent κ) Z ψ) ∧
      P (windowCauchyEvent (lossExponent κ) Z ψ) = 1) ∧
    (MeasurableSet (commonEvent N ρ a α ξ Z ψ) ∧ P (commonEvent N ρ a α ξ Z ψ) = 1) := by
  let Z := referenceAttachedModel N κ ρ a ξ (fun ε hε => (hξ ε hε).1)
  have hlift := fun (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) 1) => referenceAttachedModel_lift_ae P W hW N κ ρ hρ a ξ hξ ψ hψ hε
  have hw := window_events_measurable_measure_one P W hW κ hκE N hN ρ hρ a ξ hξ Z ψ hlift
  exact ⟨hw.1, hw.2, commonEvent_measurable_measure_one P W hW κ hκE N hN ρ hρ a
    ξ hξ Z ψ hlift α hα hκα⟩

end GlobalPhi43.Flow
