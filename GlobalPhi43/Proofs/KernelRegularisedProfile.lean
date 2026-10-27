module

public import GlobalPhi43.Proofs.RegularisedProfile
public import GlobalPhi43.Attachment.ReferenceKernel
public import GlobalPhi43.Attachment.MW20Constant

@[expose] public noncomputable section
namespace GlobalPhi43
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open Attachment MW20
open scoped NNReal ENNReal

universe u

/-- The regularised-solution profile for the fixed kernel and its deterministic
half-cylinder coefficient family. This is an alias of the shared profile choice. -/
def regularisedProfile (a η : ℝ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) : ℝ → ℝ≥0 :=
  prop32ProfileFamily.{u} referencePhi0 referencePhi0_kernelProfile
    (mw20Constant referencePhi0 referencePhi0_kernelProfile) a ρ hρ η

end GlobalPhi43
