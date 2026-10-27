module

public import GlobalPhi43.Attachment.MW20Constant
public import GlobalPhi43.Attachment.PhysicalMajorant
public import GlobalPhi43.Flow.ReferenceFlowMarkov

/-! Physical majorant bounds and the reference flow on the same full-measure event. -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.MW20
open scoped NNReal

namespace GlobalPhi43.Attachment

/-- Construction of the reference flow from a half-cylinder coefficient family.
The approximation parameter N is fixed at five. -/
theorem exists_referenceFlow_of_halfCylinderBound
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (Cdef : Kappa → ℝ≥0)
    (hhalf : ∀ κ, MW20HalfCylinderBound κ Φ hΦ (Cdef κ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2/3 : ℝ)) (-(1/2 : ℝ)))
    (hκη : κ.1 < -(1/2 : ℝ) - η)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) :
    let E := Flow.referenceEvent 5 κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)
    let A := fun sample : E => Flow.dyadicLiftData 5 κ ρ mass η ξ
      (fun ε hε => (hξ ε hε).1) sample.val sample.property
    MeasurableSet E ∧ P E = 1 ∧ ∃ u : Flow.EventFlow E η A,
      GlobalPhi43.IsContinuousMeasurableFlow E (fun t s x sample => u.value sample t s x) ∧
      GlobalPhi43.IsWindowAdapted P W (fun t s x sample => u.value sample t s x) ∧
      GlobalPhi43.IsConsistentWithTheoremA P W mass η (fun t s x sample => u.value sample t s x) ∧
      GlobalPhi43.IsTimeHomogeneous P (fun t s x sample => u.value sample t s x) ∧
      GlobalPhi43.IsFellerMarkovFlow P W (fun t s x sample => u.value sample t s x) := by
  obtain ⟨c, hc, hmajorant⟩ := reference_majorant_of_halfCylinderBound 5 κ Φ hΦ (Cdef κ) (hhalf κ)
  exact Flow.exists_referenceFlow_B1_B2_B3_B5_B6 P W hW 5 (by decide) κ hκE
    ρ hρ mass η hη hκη c hc ξ hξ
    (fun sample => hmajorant ρ mass η ξ (fun ε hε => (hξ ε hε).1) sample.val sample.property)

/-- Construction of the reference flow using the bounded-defect coefficient
family. All five asserted properties hold for the same flow. -/
theorem exists_referenceFlow_of_kernelProfile
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2/3 : ℝ)) (-(1/2 : ℝ)))
    (hκη : κ.1 < -(1/2 : ℝ) - η)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) :
    let E := Flow.referenceEvent 5 κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)
    let A := fun sample : E => Flow.dyadicLiftData 5 κ ρ mass η ξ
      (fun ε hε => (hξ ε hε).1) sample.val sample.property
    MeasurableSet E ∧ P E = 1 ∧ ∃ u : Flow.EventFlow E η A,
      GlobalPhi43.IsContinuousMeasurableFlow E (fun t s x sample => u.value sample t s x) ∧
      GlobalPhi43.IsWindowAdapted P W (fun t s x sample => u.value sample t s x) ∧
      GlobalPhi43.IsConsistentWithTheoremA P W mass η (fun t s x sample => u.value sample t s x) ∧
      GlobalPhi43.IsTimeHomogeneous P (fun t s x sample => u.value sample t s x) ∧
      GlobalPhi43.IsFellerMarkovFlow P W (fun t s x sample => u.value sample t s x) :=
  exists_referenceFlow_of_halfCylinderBound Φ hΦ (mw20Constant Φ hΦ) (mw20Constant_spec Φ hΦ)
    P W hW κ hκE ρ hρ mass η hη hκη ξ hξ

end GlobalPhi43.Attachment
