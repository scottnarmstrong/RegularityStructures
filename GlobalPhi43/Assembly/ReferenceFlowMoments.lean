module

public import GlobalPhi43.Assembly.ReferenceRegularisedMoments
public import GlobalPhi43.Assembly.ReferenceMomentInputs
public import GlobalPhi43.Assembly.ComingDown
public import GlobalPhi43.Assembly.StrongerMoments

/-! # Coming-down-from-infinity and stronger moments for a fixed reference flow -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open GlobalPhi43.Attachment
open scoped ENNReal NNReal

namespace GlobalPhi43.Assembly

universe u

section Reference

variable {Ω : Type u} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
  (a : ℝ) (η : NegExponent)
  (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))

variable (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))

variable (U : Flow.EventFlow
  (Flow.referenceEvent 5 (selectedLoss η hη.2) ρ a η ξ (fun ε hε => (hξ ε hε).1)) η
  (fun ω => Flow.dyadicLiftData 5 (selectedLoss η hη.2) ρ a η ξ
    (fun ε hε => (hξ ε hε).1) ω.val ω.property))

include W hW hρ hη ξ hξ

local notation "v" => (fun t s x ω => U.value ω t s x)

/-- Coming-down-from-infinity moments for the reference EventFlow,
with K(a,eta) fixed before the probability space. The moment estimate
and regularised majorants are derived from the reference construction. -/
theorem reference_flow_B4 : ComesDownFromInfinity P (referenceMomentProfile.{u} a η) v := by
  obtain ⟨h1, h3, h5⟩ := reference_moment_inputs P W hW ρ hρ a η hη ξ hξ U
  obtain ⟨M, hM, hb, hp⟩ := reference_regularised_majorants a η hη P W hW
  exact comesDownFromInfinity_of_reference (referenceMomentProfile.{u} a η) P W a v
    h1 h3 h5 referencePhi0 referencePhi0_isMollifier (referenceNoiseFamily P W hW)
    (fun _ he => referenceNoiseFamily_spec P W hW he) (Flow.referenceClassicalFamily P W hW a)
    (fun _ he x hx ω => Flow.referenceClassicalFamily_spec P W hW a he x hx ω) M hM hb hp

/-- Direct stronger moments of the SAME eta-flow, for every real alpha>=eta
below -1/2, including alpha=eta, and every real p>=1. No stronger flow or
compatibility premise enters; each profile is fixed before the source space. -/
theorem reference_flow_stronger_window :
    ∀ α : ℝ, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
      (⨆ r ≥ (0 : ℝ), ∫⁻ ω, strongWindowSup α v r ω ^ p ∂P) ≤
        referenceMomentProfile.{u} a α p := by
  obtain ⟨h1, h3, h5⟩ := reference_moment_inputs P W hW ρ hρ a η hη ξ hξ U
  intro α hα hα'
  obtain ⟨M, hM, hb, hm⟩ := reference_regularised_majorants a α
    ⟨lt_of_lt_of_le hη.1 hα, hα'⟩ P W hW
  intro p hp
  refine iSup_le fun r => iSup_le fun hr => ?_
  exact strongWindowSup_moment_of_homogeneity P α v h1 h5 hr
    (lt_of_lt_of_le zero_lt_one hp)
    (strongWindowSup_zero_moment (referenceMomentProfile.{u} a α) α P W a v h1 h3
      referencePhi0 referencePhi0_isMollifier (referenceNoiseFamily P W hW)
      (fun _ he => referenceNoiseFamily_spec P W hW he) (Flow.referenceClassicalFamily P W hW a)
      (fun _ he x hx ω => Flow.referenceClassicalFamily_spec P W hW a he x hx ω) M hM hb hm hp)

/-- Coming-down-from-infinity and stronger moments for the specified flow,
with the regularised-solution moment profile. No invariant measure is selected. -/
theorem reference_flow_B4_and_stronger :
    ComesDownFromInfinity P (regularisedProfile.{u} a η referencePhi0 referencePhi0_isMollifier) v ∧
    ∀ α : ℝ, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
      (⨆ r ≥ (0 : ℝ), ∫⁻ ω, strongWindowSup α v r ω ^ p ∂P) ≤
        regularisedProfile.{u} a α referencePhi0 referencePhi0_isMollifier p := by
  exact ⟨reference_flow_B4 P W hW ρ hρ a η hη ξ hξ U,
    reference_flow_stronger_window P W hW ρ hρ a η hη ξ hξ U⟩

end Reference

end GlobalPhi43.Assembly
