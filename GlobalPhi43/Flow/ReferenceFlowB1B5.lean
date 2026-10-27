module

public import GlobalPhi43.Flow.ReferenceFlowB1
public import GlobalPhi43.Flow.ReferenceFlowAssembly
public import GlobalPhi43.Flow.ReferenceHomogeneity

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- A reference flow on one measurable full event with joint measurability,
restart and time homogeneity, under the every-start majorant assumption. -/
theorem exists_referenceFlow_B1_B5 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η) (c : ℝ) (hc : 0 ≤ c)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (hmajorant : ∀ ω : referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1),
      EveryStartMajorant c (dyadicLiftData N κ ρ mass η ξ
        (fun ε hε => (hξ ε hε).1) ω.val ω.property)) :
    let E := referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)
    let A := fun ω : E => dyadicLiftData N κ ρ mass η ξ
      (fun ε hε => (hξ ε hε).1) ω.val ω.property
    MeasurableSet E ∧ P E = 1 ∧ ∃ u : EventFlow E η A,
      GlobalPhi43.IsContinuousMeasurableFlow E (fun t s x ω => u.value ω t s x) ∧
      GlobalPhi43.IsTimeHomogeneous P (fun t s x ω => u.value ω t s x) := by
  obtain ⟨hE, hfull⟩ := referenceEvent_measurable_measure_one P W hW N hN κ hκE
    ρ hρ mass η hη hκη ξ hξ
  obtain ⟨u⟩ := exists_referenceEventFlow N hN κ hκE ρ mass η hη hκη c hc ξ
    (fun ε hε => (hξ ε hε).1) hmajorant
  exact ⟨hE, hfull, u,
    referenceEventFlow_B1 P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u,
    referenceEventFlow_isTimeHomogeneous P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u⟩

end GlobalPhi43.Flow
