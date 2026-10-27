module

public import GlobalPhi43.Compatibility.ReferenceTargets
public import GlobalPhi43.Attachment.ReferencePhysicalFlow

/-! Selection of reference flows from the physical estimates. -/

public noncomputable section
namespace GlobalPhi43.Compatibility
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set

/-- One family of reference flows satisfying the deterministic half-cylinder bounds.
The mollifier, mass and noise family are fixed before the target and its selected loss. -/
def selectedReferenceFamily (Φ : ParabolicSpace → ℝ) (hΦ : MW20.KernelProfile Φ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0:ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) :
    (η : Target) → ReferenceAt ρ a ξ (fun ε hε => (hξ ε hε).1) η :=
  fun η => (Attachment.exists_referenceFlow_of_kernelProfile Φ hΦ P W hW
    (targetLoss η) (targetLoss_spec η).1 ρ hρ a η.1 η.2 (targetLoss_spec η).2 ξ hξ).2.2.choose

end GlobalPhi43.Compatibility
