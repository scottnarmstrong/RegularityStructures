module

public import GlobalPhi43.Flow.ReferenceFlowB3
public import GlobalPhi43.Flow.ReferenceFlowB1
public import GlobalPhi43.Flow.ReferenceHomogeneity
public import GlobalPhi43.Attachment.AdmissibleLoss

/-! # Joint continuity, measurability, consistency and time homogeneity of the reference flow -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Assembly

/-- For N=5 and the target-only selected loss, the supplied actual reference
EventFlow is jointly continuous and measurable, consistent with regularised
solutions and time homogeneous. No stronger-target flow, compatibility
or moment estimate is assumed. -/
theorem reference_moment_inputs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : Flow.EventFlow
      (Flow.referenceEvent 5 (Attachment.selectedLoss η hη.2) ρ mass η ξ
        (fun ε hε => (hξ ε hε).1)) η
      (fun ω => Flow.dyadicLiftData 5 (Attachment.selectedLoss η hη.2) ρ mass η ξ
        (fun ε hε => (hξ ε hε).1) ω.val ω.property)) :
    let E := Flow.referenceEvent 5 (Attachment.selectedLoss η hη.2) ρ mass η ξ
      (fun ε hε => (hξ ε hε).1)
    let v := fun t s x ω => u.value ω t s x
    IsContinuousMeasurableFlow E v ∧ IsConsistentWithTheoremA P W mass η v ∧
      IsTimeHomogeneous P v := by
  have hκ := Attachment.selectedLoss_spec η hη.2
  exact ⟨Flow.referenceEventFlow_B1 P W hW 5 (by norm_num) _ hκ.1
      ρ hρ mass η hη hκ.2 ξ hξ u,
    Flow.referenceEventFlow_B3 P W hW 5 (by norm_num) _ hκ.1
      ρ hρ mass η hη hκ.2 ξ hξ u,
    Flow.referenceEventFlow_isTimeHomogeneous P W hW 5 (by norm_num) _ hκ.1
      ρ hρ mass η hη hκ.2 ξ hξ u⟩

end GlobalPhi43.Assembly
