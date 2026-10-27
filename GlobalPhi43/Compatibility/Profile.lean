module

public import GlobalPhi43.Proofs.KernelRegularisedProfile
public import GlobalPhi43.Proofs.GlobalDynamicsProfile
public import GlobalPhi43.Attachment.MW20Constant
public import GlobalPhi43.Attachment.ReferenceKernel
public import GlobalPhi43.Compatibility.ReferenceTargets

/-! The exact shared deterministic profile at the fixed reference inputs. -/

public noncomputable section
namespace GlobalPhi43.Compatibility
open RegularityStructures Set Attachment
open scoped NNReal
universe u

/-- A definitional specialization of the shared profile family, with no additional selection. -/
@[expose] def compatibilityProfile (a : ℝ) (η : NegExponent) : ℝ → ℝ≥0 :=
  prop32ProfileFamily.{u} referencePhi0 referencePhi0_kernelProfile
    (mw20Constant referencePhi0 referencePhi0_kernelProfile) a
    referencePhi0 referencePhi0_isMollifier η

/-- The specified reference global flow uses exactly this same profile. -/
theorem compatibilityProfile_eq_globalDynamicsProfile (a : ℝ) (η : NegExponent) :
    compatibilityProfile.{u} a η = globalDynamicsProfile.{u} a η := rfl

end GlobalPhi43.Compatibility
