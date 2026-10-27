module

public import GlobalPhi43.Compatibility.CommonReferenceFamily
public import GlobalPhi43.Compatibility.Profile
public import GlobalPhi43.Flow.ReferenceGlobalFlow

/-! Global-flow properties for the specified common reference objects.
One law is selected after each flow. -/

public noncomputable section
namespace GlobalPhi43.Compatibility
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set Attachment
universe u

theorem commonReferenceFamily_global (a : ℝ) (η : Target)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) :
    ∃ μ : Measure (HolderBesov η.1),
      IsGlobalPhi43Flow (compatibilityProfile.{u} a η.1) P W a η.1
        (Flow.referenceEvent 5 (targetLoss η) referencePhi0 a η.1
          (referenceNoiseFamily P W hW) (fun _ hε => (referenceNoiseFamily_spec P W hW hε).1))
        (fun t s x ω => (commonReferenceFamily a P W hW η).value ω t s x) μ := by
  obtain ⟨μ,hglobal,_⟩ := Flow.referenceEventFlow_global P W hW
    referencePhi0 referencePhi0_isMollifier a η.1 η.2 (referenceNoiseFamily P W hW)
    (fun _ hε => referenceNoiseFamily_spec P W hW hε) (commonReferenceFamily a P W hW η)
  refine ⟨(μ : Measure _),?_⟩
  rw [compatibilityProfile_eq_globalDynamicsProfile]
  exact hglobal

end GlobalPhi43.Compatibility
