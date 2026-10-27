module

public import GlobalPhi43.Attachment.ReferenceIntegerMoments
public import GlobalPhi43.Attachment.SeventhMomentProfile
public import GlobalPhi43.Attachment.AdmissibleLoss

/-! # A single source real-p profile, before every noise space and regularisation family -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

universe u

/-- Actual reference Q_epsilon moments, for all real p>=1 and ALL epsilon in (0,1].
The single profile is selected before Omega,P,W,xi, not once per probability space. -/
theorem reference_seventh_profile (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ) (c : ℝ≥0) :
    ∃ C : ℝ → ℝ≥0,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ), IsWhiteNoise P W →
      ∀ (ξ : ℝ → Ω → SpaceTime → ℝ)
        (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)),
      let Z := Flow.referenceAttachedModel 5 κ ρ mass ξ (fun ε hε => (hξ ε hε).1)
      let ψ := Flow.referencePotential ξ (fun ε hε => (hξ ε hε).1)
      ∀ p : ℝ, 1 ≤ p →
        (⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω,
          ((c : ℝ≥0∞) * (1 + (Z ε ω).normOn (gamma κ) (Flow.majorantRegion 0) +
            Flow.unitPotentialSize (Flow.lossExponent κ) 0 (ψ ε ω)) ^ 7) ^ p ∂P) ≤ C p := by
  obtain ⟨CX, CY, h⟩ := reference_integer_profiles.{u} κ hκE ρ hρ mass
  refine ⟨seventhMomentProfile c CX CY, ?_⟩
  intro Ω _ P _ W hW ξ hξ
  dsimp only
  intro p hp
  refine iSup_le fun ε => iSup_le fun he => ?_
  have hi := h P W hW ξ hξ
  exact seventh_moment_le c CX CY P _ _ (hi 1 le_rfl ε he).1
    (fun n hn => (hi n hn ε he).2.1) (fun n hn => (hi n hn ε he).2.2) hp

end GlobalPhi43.Attachment
