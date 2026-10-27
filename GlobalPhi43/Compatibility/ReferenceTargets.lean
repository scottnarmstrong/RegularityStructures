module

public import GlobalPhi43.Attachment.AdmissibleLoss
public import GlobalPhi43.Flow.PhysicalTargetCompatibility

/-! Target-dependent loss selection and reference flows for compatibility across exponents. -/

@[expose] public noncomputable section
namespace GlobalPhi43.Compatibility
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set

/-- Only the source target interval is constrained; no off-range EventFlow is needed. -/
def Target := {η : NegExponent // (η : ℝ) ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ))}

def targetLoss (η : Target) : Kappa := Attachment.selectedLoss η.1 η.2.2

theorem targetLoss_spec (η : Target) : Attachment.AdmissibleLoss η.1 (targetLoss η) :=
  Attachment.selectedLoss_spec η.1 η.2.2

/-- This type retains the literal source event and dyadic approximants, at N=5. -/
abbrev ReferenceAt {Ω : Type*} (ρ : ParabolicSpace → ℝ) (a : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0:ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω)) (η : Target) :=
  Flow.EventFlow (Flow.referenceEvent 5 (targetLoss η) ρ a η.1 ξ hξ) η.1
    (fun ω => Flow.dyadicLiftData 5 (targetLoss η) ρ a η.1 ξ hξ ω.val ω.property)

/-- Simultaneous physical comparison for each fixed pair of chosen reference flows.
No intersection over the uncountable target family is formed. -/
theorem referenceFamily_pair_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0:ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (U : (η : Target) → ReferenceAt ρ a ξ (fun ε hε => (hξ ε hε).1) η)
    (η γ : Target) (hηγ : (η.1 : ℝ) < γ.1) :
    ∀ᵐ ω ∂P, ∀ s t, 0≤s → s≤t → ∀ x : HolderBesov γ.1,
      holderBesovEmbed η.1 γ.1 hηγ.le ((U γ).value ω t s x) =
        (U η).value ω t s (holderBesovEmbed η.1 γ.1 hηγ.le x) := by
  have h := (Flow.referenceFlow_targets_ae P W hW
    (targetLoss η) (targetLoss_spec η).1 (targetLoss γ) (targetLoss_spec γ).1
    ρ hρ a η.1 γ.1 η.2 γ.2 hηγ (targetLoss_spec η).2 (targetLoss_spec γ).2
    ξ hξ (U η) (U γ)).1
  exact h.mono fun ω h s t hs hst x => (h s t hs hst x).symm

end GlobalPhi43.Compatibility
