module

public import GlobalPhi43.Proofs.RegularisedProfile
public import GlobalPhi43.Attachment.ReferenceKernel
public import GlobalPhi43.Attachment.MW20Constant

public noncomputable section

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43 Attachment
open scoped NNReal

universe u

/-- The global-flow profile `K(a,η)`, a transparent specialization of the shared
regularised-solution profile family, with no additional profile choice.
It is total in η, so compatibility can select the entire family before the space. -/
@[expose] def globalDynamicsProfile (a η : ℝ) : ℝ → ℝ≥0 :=
  prop32ProfileFamily.{u} referencePhi0 referencePhi0_kernelProfile
    (mw20Constant referencePhi0 referencePhi0_kernelProfile) a
    referencePhi0 referencePhi0_isMollifier η

end GlobalPhi43
