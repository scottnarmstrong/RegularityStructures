module

public import GlobalPhi43.Attachment.MW20DefectConstant
public import GlobalPhi43.Proofs.MW20DefectBound

/-! The bounded-defect estimate supplies a shared deterministic coefficient
family for the physical majorant bounds. -/

public noncomputable section

open RegularityStructures RegularityStructures.Phi43 GlobalPhi43.MW20
open scoped NNReal

namespace GlobalPhi43.Attachment

/-- The full real-loss, all-radius conclusion, obtained from the bounded-defect theorem. -/
theorem hasMW20DefectBound_of_kernelProfile (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    HasMW20DefectBound Φ :=
  GlobalPhi43.mw20DefectBound Φ (isMWTestKernel_of_kernelProfile hΦ)

/-- Shared deterministic family, selected before targets and noise spaces. -/
@[expose] def mw20Constant (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) : Kappa → ℝ≥0 :=
  HasMW20DefectBound.constant Φ (hasMW20DefectBound_of_kernelProfile Φ hΦ)

/-- The common coefficient family satisfies the half-cylinder bound. -/
theorem mw20Constant_spec (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∀ κ, MW20HalfCylinderBound κ Φ hΦ (mw20Constant Φ hΦ κ) :=
  HasMW20DefectBound.halfCylinderBound Φ hΦ (hasMW20DefectBound_of_kernelProfile Φ hΦ)

end GlobalPhi43.Attachment
