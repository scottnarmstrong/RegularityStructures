module

public import GlobalPhi43.Flow.TargetCompatibility
public import GlobalPhi43.Flow.DyadicLiftData

/-! # Target compatibility on the intersection of the two original reference events -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- The same reference noise/renormalisation family is used at both targets.
Lift orders and admissible losses may differ; moderate representatives are not identified. -/
theorem referenceFlow_target_compatibility {Ω : Type*}
    (N M : ℕ) (κ κ' : Kappa) (ρ : ParabolicSpace → ℝ) (mass : ℝ)
    (η γ : NegExponent) (hηγ : (η : ℝ) ≤ γ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (u : EventFlow (referenceEvent N κ ρ mass η ξ hsmooth) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ hsmooth ω.val ω.property))
    (v : EventFlow (referenceEvent M κ' ρ mass γ ξ hsmooth) γ
      (fun ω => dyadicLiftData M κ' ρ mass γ ξ hsmooth ω.val ω.property))
    (ω : Ω) (hω : ω ∈ referenceEvent N κ ρ mass η ξ hsmooth ∩
      referenceEvent M κ' ρ mass γ ξ hsmooth)
    (s t : ℝ) (hst : s ≤ t) (x : HolderBesov γ) :
    u.value ω t s (holderBesovEmbed η γ hηγ x) =
      holderBesovEmbed η γ hηγ (v.value ω t s x) :=
  u.target_compatibility hηγ v ω hω.1 hω.2 (fun _ => rfl) (fun _ => rfl) s t hst x

/-- Compatibility on the same events. The intersection is exactly the two
original events, selected before all real starts and rough data. The two
EventFlow witnesses are fixed inputs of this theorem. -/
theorem referenceFlow_targets_on_common_event {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (M : ℕ) (hM : 5 ≤ M) (κ' : Kappa) (hκ'E : κ'.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η γ : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hγ : (γ : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))) (hηγ : (η : ℝ) < γ)
    (hκη : κ.1 < -(1 / 2 : ℝ) - η) (hκγ : κ'.1 < -(1 / 2 : ℝ) - γ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : EventFlow (referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property))
    (v : EventFlow (referenceEvent M κ' ρ mass γ ξ (fun ε hε => (hξ ε hε).1)) γ
      (fun ω => dyadicLiftData M κ' ρ mass γ ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property)) :
    let E := referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)
    let F := referenceEvent M κ' ρ mass γ ξ (fun ε hε => (hξ ε hε).1)
    MeasurableSet (E ∩ F) ∧ P (E ∩ F) = 1 ∧
      ∀ ω ∈ E ∩ F, ∀ s t : ℝ, s ≤ t → ∀ x : HolderBesov γ,
        u.value ω t s (holderBesovEmbed η γ hηγ.le x) =
          holderBesovEmbed η γ hηγ.le (v.value ω t s x) := by
  obtain ⟨hE, hpE⟩ := referenceEvent_measurable_measure_one P W hW N hN κ hκE
    ρ hρ mass η hη hκη ξ hξ
  obtain ⟨hF, hpF⟩ := referenceEvent_measurable_measure_one P W hW M hM κ' hκ'E
    ρ hρ mass γ hγ hκγ ξ hξ
  refine ⟨hE.inter hF, ?_, ?_⟩
  · exact (mem_ae_iff_prob_eq_one (hE.inter hF)).mp
      (Filter.inter_mem ((mem_ae_iff_prob_eq_one hE).mpr hpE)
        ((mem_ae_iff_prob_eq_one hF).mpr hpF))
  · intro ω hω s t hst x
    exact referenceFlow_target_compatibility N M κ κ' ρ mass η γ hηγ.le ξ
      (fun ε hε => (hξ ε hε).1) u v ω hω s t hst x

end GlobalPhi43.Flow
