module

public import GlobalPhi43.Compatibility.ReferenceFamilySelection
public import GlobalPhi43.Attachment.ReferenceInputs

/-! One actual common reference family for every target, from fixed reference inputs. -/

public noncomputable section
namespace GlobalPhi43.Compatibility
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set
open Attachment

/-- Noise and mollifier are common across all targets, indeed xi precedes the mass. -/
def commonReferenceFamily (a : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) :
    (η : Target) → ReferenceAt referencePhi0 a (referenceNoiseFamily P W hW)
      (fun _ hε => (referenceNoiseFamily_spec P W hW hε).1) η :=
  selectedReferenceFamily referencePhi0 referencePhi0_kernelProfile P W hW
    referencePhi0 referencePhi0_isMollifier a (referenceNoiseFamily P W hW)
    (fun _ hε => referenceNoiseFamily_spec P W hW hε)

end GlobalPhi43.Compatibility
