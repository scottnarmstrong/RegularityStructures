module

public import GlobalPhi43.Flow.ReferenceFlowKernel
public import GlobalPhi43.Flow.ReferenceFeller
public import GlobalPhi43Statements.Defs.IsFellerMarkovFlow

public noncomputable section

open MeasureTheory ProbabilityTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

section Reference

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
  (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
  (hκη : κ.1 < -(1 / 2 : ℝ) - η)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))

include hW hN hκE hρ hη hκη

local notation "E" => referenceEvent N κ ρ mass η ξ (fun ε hε => And.left (hξ ε hε))
local notation "A" => (fun ω : E => dyadicLiftData N κ ρ mass η ξ
  (fun ε hε => And.left (hξ ε hε)) (Subtype.val ω) (Subtype.property ω))

/-- The Feller Markov property for the same reference flow. Its probabilistic
hypotheses follow from the white noise and the reference-flow construction. -/
theorem referenceEventFlow_B6 (u : EventFlow E η A) :
    GlobalPhi43.IsFellerMarkovFlow P W (fun t s x ω => u.value ω t s x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    exact Markov.flowLaw_isProbabilityMeasure
      (referenceFlow_sample_measurable P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u t ht x)
  · intro B hB
    exact Markov.measurable_flowLaw_of_joint
      (referenceFlow_samples_measurable P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u) hB
  · intro x
    exact Markov.flowLaw_zero_eq_dirac x (fun ω => u.initial ω 0 le_rfl x)
  · exact referenceFlow_chapmanKolmogorov P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u
  · intro f hf hb s t hs ht x
    obtain ⟨C, hC⟩ := hb
    exact referenceFlow_condExp P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u s t hs ht x hf hC
  · intro f
    obtain ⟨hspace, htime⟩ := referenceFlow_feller P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u f
    exact ⟨fun t ht => ⟨(hspace t ht).1, ‖f‖, (hspace t ht).2⟩, htime⟩

end Reference
end GlobalPhi43.Flow
