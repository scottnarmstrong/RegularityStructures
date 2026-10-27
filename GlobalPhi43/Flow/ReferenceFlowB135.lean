module

public import GlobalPhi43.Flow.ReferenceFlowB3
public import GlobalPhi43.Flow.ReferenceFlowB1B5

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- A reference flow on one measurable full event, with joint measurability,
restart, regularisation convergence and time homogeneity, under the every-start majorant
assumption. The majorant, coming-down estimate and Markov property are not conclusions
of this lemma. -/
theorem exists_referenceFlow_B1_B3_B5 {Ω : Type*} [MeasurableSpace Ω]
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
      GlobalPhi43.IsConsistentWithTheoremA P W mass η (fun t s x ω => u.value ω t s x) ∧
      GlobalPhi43.IsTimeHomogeneous P (fun t s x ω => u.value ω t s x) := by
  obtain ⟨hE, hfull, u, hB1, hB5⟩ := exists_referenceFlow_B1_B5 P W hW N hN κ hκE
    ρ hρ mass η hη hκη c hc ξ hξ hmajorant
  exact ⟨hE, hfull, u, hB1,
    referenceEventFlow_B3 P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u, hB5⟩

end GlobalPhi43.Flow
