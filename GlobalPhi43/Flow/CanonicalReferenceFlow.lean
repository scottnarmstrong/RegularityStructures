module

public import GlobalPhi43.Attachment.ReferenceInputs
public import GlobalPhi43.Attachment.ReferencePhysicalFlow
public import GlobalPhi43.Attachment.AdmissibleLoss

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

open Attachment

/-- The reference flow for a target, constructed from the fixed kernel, mollifier,
and noise family. The noise family is independent of the target. The flow constructor
is invoked exactly once; no invariant law is chosen here, so this object can also be
used for pairwise compatibility. -/
theorem exists_canonical_referenceFlow (a : ℝ) (η : NegExponent)
    (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) :
    let ξ := referenceNoiseFamily P W hW
    let hs := fun ε (hε : ε ∈ Ioc (0 : ℝ) 1) =>
      And.left (referenceNoiseFamily_spec P W hW hε)
    let E := referenceEvent 5 (selectedLoss η hη.2) referencePhi0 a η ξ hs
    let A := fun sample : E => dyadicLiftData 5 (selectedLoss η hη.2)
      referencePhi0 a η ξ hs sample.val sample.property
    Nonempty (EventFlow E η A) := by
  have hκ := selectedLoss_spec η hη.2
  obtain ⟨_, _, u, _⟩ := exists_referenceFlow_of_kernelProfile referencePhi0 referencePhi0_kernelProfile
    P W hW (selectedLoss η hη.2) hκ.1 referencePhi0 referencePhi0_isMollifier a
    η hη hκ.2 (referenceNoiseFamily P W hW)
    (fun _ hε => referenceNoiseFamily_spec P W hW hε)
  exact ⟨u⟩

end GlobalPhi43.Flow
