module

public import GlobalPhi43.Flow.ReferenceMarkovInputs

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped BoundedContinuousFunction

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

/-- Feller continuity, the uniform contraction bound, and continuous time
dependence all follow from the actual producer's continuity and measurability. -/
theorem referenceFlow_feller (u : EventFlow E η A) (f : HolderBesov η →ᵇ ℝ) :
    (∀ t, 0 ≤ t → Continuous (flowTransition P (fun t s x ω => u.value ω t s x) t f) ∧
      ∀ x, |flowTransition P (fun t s x ω => u.value ω t s x) t f x| ≤ ‖f‖) ∧
    ∀ x, ContinuousOn (fun t => flowTransition P (fun t s x ω => u.value ω t s x) t f x) (Ici 0) := by
  constructor
  · intro t ht
    have hm := referenceFlow_sample_measurable P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u t ht
    exact ⟨Markov.continuous_flowTransition_of_samples hm
      (ae_of_all _ (fun ω => u.continuous_datum ω le_rfl ht)) f,
      fun x => Markov.abs_flowTransition_le hm f x⟩
  · intro x
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact Markov.continuous_time_flowTransition_of_samples x
      (fun t => referenceFlow_sample_measurable P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ
        u t.val t.property x)
      (ae_of_all _ (fun ω => (u.globalPath ω 0 le_rfl x).continuous)) f

end Reference
end GlobalPhi43.Flow
