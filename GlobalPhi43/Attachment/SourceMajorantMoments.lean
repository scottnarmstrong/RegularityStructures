module

public import GlobalPhi43.Attachment.SourceMajorantComparison
public import GlobalPhi43.Attachment.ReferenceSeventhMoments

/-! A moment profile for the source majorant from a time-slice bound. -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

universe u

/-- The everywhere-defined majorant M has a real-p moment profile chosen before
the probability space. The time-slice inequality is an analytic hypothesis;
no moment or solution-cover estimate is assumed. -/
theorem sourceMajorant_profile_of_slice (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ) (c H : ℝ≥0)
    (hslice : ∀ (a : Flow.LiftData 5 κ) (s : ℝ), 0 ≤ s → ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt t) * holderBesovENorm (Flow.lossExponent κ)
        (smoothNoiseJ 5 ⟨a.forcing, Flow.smooth_of_moderateLift a.moderate⟩ (s+t)) ≤
      (H : ℝ≥0∞) * (Flow.unitPotentialSize (Flow.lossExponent κ) s a.potential +
        (1+a.model.normOn (gamma κ) (Flow.majorantRegion s))^3)) :
    ∃ C : ℝ → ℝ≥0,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ), IsWhiteNoise P W →
      ∀ (ξ : ℝ → Ω → SpaceTime → ℝ)
        (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)),
      let M := sourceMajorant κ Φ hΦ ρ mass c ξ (fun ε hε => (hξ ε hε).1)
      (∀ ε, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω) ∧
      ∀ p : ℝ, 1 ≤ p →
        (⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P) ≤ C p := by
  obtain ⟨K, hcompare⟩ := sourceMajorant_comparison_of_slice.{u} κ Φ hΦ c H hslice
  obtain ⟨C, hprofile⟩ := reference_seventh_profile.{u} κ hκE ρ hρ mass
    (majorantCoefficient c K H)
  refine ⟨C, ?_⟩
  intro Ω _ P _ W hW ξ hξ
  dsimp only
  refine ⟨fun ε => sourceMajorant_measurable_nonneg ξ hξ κ Φ hΦ mass c ε, ?_⟩
  intro p hp
  refine iSup_le fun ε => iSup_le fun he => ?_
  obtain ⟨hG, hpG⟩ := growthEvent_measurable_measure_one P W hW ρ hρ he (ξ ε) (hξ ε he)
  have hae : ∀ᵐ ω ∂P, ω ∈ growthEvent (ξ ε) := (mem_ae_iff_prob_eq_one hG).mpr hpG
  have hb := hae.mono fun ω hω => ENNReal.rpow_le_rpow
    (hcompare ρ mass ξ (fun e h => (hξ e h).1) ε he ω hω) (le_trans zero_le_one hp)
  exact (lintegral_mono_ae hb).trans
    ((le_iSup₂_of_le ε he le_rfl).trans (hprofile P W hW ξ hξ p hp))

end GlobalPhi43.Attachment
