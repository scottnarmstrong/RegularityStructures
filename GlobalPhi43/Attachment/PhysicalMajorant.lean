module

public import GlobalPhi43.Attachment.CoverOfHalfCylinderBound
public import GlobalPhi43.Attachment.ActualSliceRowBound

/-! Physical majorants from the bounded-defect half-cylinder estimate.
The same-exponent slice, local-data scaling and functional bounds hold uniformly
before the choices of starts, initial data and random outcomes. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.MW20
open scoped NNReal

namespace GlobalPhi43.Attachment

/-- Physical majorant bound assuming the bounded-defect half-cylinder estimate;
the time-slice bound follows from the deterministic slice estimates. -/
theorem everyStartMajorant_of_halfCylinderBound (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (C : ℝ≥0)
    (hhalf : MW20HalfCylinderBound κ Φ hΦ C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ A : ℕ → Flow.LiftData N κ, Flow.EveryStartMajorant c A := by
  obtain ⟨H, hslice⟩ := exists_actualSliceRow N κ
  exact everyStartMajorant_of_halfCylinderBound_of_slice N κ Φ hΦ C H hhalf hslice

/-- Assuming the bounded-defect half-cylinder estimate, one coefficient works
for all regularised noises, starting times and initial data. -/
theorem reference_majorant_of_halfCylinderBound (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (C : ℝ≥0)
    (hhalf : MW20HalfCylinderBound κ Φ hΦ C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Ω : Type*} (ρ : ParabolicSpace → ℝ) (mass α : ℝ)
      (ξ : ℝ → Ω → SpaceTime → ℝ)
      (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ sample, IsSmoothOnSpaceTime (ξ ε sample))
      (sample : Ω) (hE : sample ∈ Flow.referenceEvent N κ ρ mass α ξ hsmooth),
      Flow.EveryStartMajorant c (Flow.dyadicLiftData N κ ρ mass α ξ hsmooth sample hE) := by
  obtain ⟨c, hc, h⟩ := everyStartMajorant_of_halfCylinderBound N κ Φ hΦ C hhalf
  refine ⟨c, hc, ?_⟩
  intro Ω ρ mass α ξ hsmooth sample hE
  exact h _

end GlobalPhi43.Attachment
