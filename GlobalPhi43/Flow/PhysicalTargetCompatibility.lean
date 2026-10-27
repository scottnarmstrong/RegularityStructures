module

public import GlobalPhi43.Flow.ReferenceTargetCompatibility

/-! # Physical target comparison at N=5, and simultaneous almost-sure consequences -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Both the physical and total-map comparisons hold on the same original
full event intersection, before any starts, times or rough data are given.
The all-real component uses only the existing negative-start identity branch. -/
theorem referenceFlow_targets_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (κ' : Kappa) (hκ'E : κ'.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η γ : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hγ : (γ : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))) (hηγ : (η : ℝ) < γ)
    (hκη : κ.1 < -(1 / 2 : ℝ) - η) (hκγ : κ'.1 < -(1 / 2 : ℝ) - γ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : EventFlow (referenceEvent 5 κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) η
      (fun ω => dyadicLiftData 5 κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property))
    (v : EventFlow (referenceEvent 5 κ' ρ mass γ ξ (fun ε hε => (hξ ε hε).1)) γ
      (fun ω => dyadicLiftData 5 κ' ρ mass γ ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property)) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ x : HolderBesov γ,
      u.value ω t s (holderBesovEmbed η γ hηγ.le x) =
        holderBesovEmbed η γ hηγ.le (v.value ω t s x)) ∧
    (∀ᵐ ω ∂P, ∀ s t : ℝ, s ≤ t → ∀ x : HolderBesov γ,
      u.value ω t s (holderBesovEmbed η γ hηγ.le x) =
        holderBesovEmbed η γ hηγ.le (v.value ω t s x)) := by
  obtain ⟨hE, hpE, hcomp⟩ := referenceFlow_targets_on_common_event P W hW
    5 le_rfl κ hκE 5 le_rfl κ' hκ'E ρ hρ mass η γ hη hγ hηγ hκη hκγ ξ hξ u v
  have hevent := (mem_ae_iff_prob_eq_one hE).mpr hpE
  have hall : ∀ᵐ ω ∂P, ∀ s t : ℝ, s ≤ t → ∀ x : HolderBesov γ,
      u.value ω t s (holderBesovEmbed η γ hηγ.le x) =
        holderBesovEmbed η γ hηγ.le (v.value ω t s x) := by
    filter_upwards [hevent] with ω hω
    exact hcomp ω hω
  exact ⟨hall.mono fun _ h s t _ hst x => h s t hst x, hall⟩

end GlobalPhi43.Flow
