module

public import GlobalPhi43.Flow.ReferenceMollifierLimit
public import GlobalPhi43Statements.Defs.IsConsistentWithTheoremA

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Regularisation convergence for every admissible mollifier and noise family,
and every smooth datum and classical approximant family, quantified after the fixed
reference flow. No mollifier-dependent flow or event is selected. -/
theorem referenceEventFlow_B3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : EventFlow (referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property)) :
    GlobalPhi43.IsConsistentWithTheoremA P W mass η (fun t s x ω => u.value ω t s x) := by
  intro ρ' hρ' ξ' hξ' x hx U hU
  have hξ0 : ∀ ε ∈ Ioc (0 : ℝ) 1,
      IsRegularisedNoise P (shiftWhiteNoise W 0) ρ' ε (ξ' ε) := by
    simpa only [shiftWhiteNoise_zero] using hξ'
  have hlim := referenceFlow_limit_any_mollifier P W hW N hN κ hκE ρ hρ mass η hη hκη
    ξ hξ u 0 le_rfl ρ' hρ' ξ' hξ0 x hx U hU
  have hlim' : IsPhi43Limit P η x U (fun _ => ⊤)
      (fun ω t => u.value ω t 0 (toHolderBesov η x)) := by
    simpa only [zero_add] using hlim
  refine ⟨?_, hlim'⟩
  intro T hT δ hδ
  simpa only [ENNReal.ofReal_lt_top, true_and] using hlim'.converges T hT δ hδ

end GlobalPhi43.Flow
