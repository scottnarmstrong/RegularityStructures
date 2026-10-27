module

public import GlobalPhi43.Attachment.MajorantSliceComparison
public import GlobalPhi43.Attachment.SourceMajorantMoments

/-! # Moments of the actual everywhere-defined source majorant -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

universe u

/-- Slice bounds discharge the final analytic premise. The profile is chosen
before the probability space; physical solution-cover domination is separate. -/
theorem sourceMajorant_profile (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ) (c : ℝ≥0) :
    ∃ C : ℝ → ℝ≥0,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ), IsWhiteNoise P W →
      ∀ (ξ : ℝ → Ω → SpaceTime → ℝ)
        (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)),
      let M := sourceMajorant κ Φ hΦ ρ mass c ξ (fun ε hε => (hξ ε hε).1)
      (∀ ε, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω) ∧
      ∀ p : ℝ, 1 ≤ p →
        (⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P) ≤ C p := by
  obtain ⟨H, hH⟩ := majorant_slice_row κ
  exact sourceMajorant_profile_of_slice.{u} κ hκE Φ hΦ ρ hρ mass c H hH

/-- The construction loss is chosen from the target alone, before the source
probability space. The slice and moment estimates follow from the deterministic bounds. -/
theorem selected_sourceMajorant_profile (η' : ℝ) (hη' : η' < -(1 / 2 : ℝ))
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ) (c : Kappa → ℝ≥0) :
    let κ := selectedLoss η' hη'
    AdmissibleLoss η' κ ∧ ∃ C : ℝ → ℝ≥0,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ), IsWhiteNoise P W →
      ∀ (ξ : ℝ → Ω → SpaceTime → ℝ)
        (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)),
      let M := sourceMajorant κ Φ hΦ ρ mass (c κ) ξ (fun ε hε => (hξ ε hε).1)
      (∀ ε, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω) ∧
      ∀ p : ℝ, 1 ≤ p →
        (⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P) ≤ C p := by
  exact ⟨selectedLoss_spec η' hη', sourceMajorant_profile.{u}
    (selectedLoss η' hη') (selectedLoss_spec η' hη').1 Φ hΦ ρ hρ mass
    (c (selectedLoss η' hη'))⟩

end GlobalPhi43.Attachment
