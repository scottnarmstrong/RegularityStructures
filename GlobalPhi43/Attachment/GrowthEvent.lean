module

public import GlobalPhi43.Attachment.Model
public import Phi43.Stochastic.StochasticHeatConvergenceGrowthMeasurable

/-! Measurability and full measure of the model-convergence event. -/

public section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures RegularityStructures.Phi43

/-- The exact polynomial-growth event is measurable and has probability one. -/
theorem growthEvent_measurable_measure_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (ξ : Ω → SpaceTime → ℝ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) :
    MeasurableSet (growthEvent ξ) ∧ P (growthEvent ξ) = 1 := by
  obtain ⟨hm, hae⟩ := regularisedNoise_hasPhi43NoiseGrowth_measurable_ae P W hW ρ hρ hε ξ hξ
  refine ⟨hm, ?_⟩
  exact (prob_compl_eq_zero_iff hm).mp (ae_iff.mp hae)

end GlobalPhi43.Attachment
