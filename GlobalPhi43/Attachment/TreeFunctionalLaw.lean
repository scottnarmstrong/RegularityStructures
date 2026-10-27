module

public import GlobalPhi43.Attachment.TreeFunctionalMeasurable
public import GlobalPhi43.Attachment.SmoothNoiseSliceLaw

/-! Everywhere observable laws on the full smooth-noise evaluation space.
The separate C-infinity Polish topology is not asserted here. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43 Local MW20 Set

/-- Full functional measurability and finiteness at every outcome of a smooth noise family. -/
theorem noiseFunctional_measurable_finite {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) (hS : IsCompact S)
    (ξ : Ω → SpaceTime → ℝ) (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω))
    (hm : ∀ z, Measurable fun ω => ξ ω z) :
    Measurable (fun ω => attachmentFunctional N κ Φ hΦ (ξ ω) C S) ∧
      ∀ ω, attachmentFunctional N κ Φ hΦ (ξ ω) C S < ⊤ := by
  constructor
  · have h := (attachmentFunctional_measurable N κ Φ hΦ C S).comp
      (asSmoothNoise_measurable ξ hs hm)
    simpa only [Function.comp_def, asSmoothNoise] using h
  · exact fun ω => lt_top_iff_ne_top.mpr (attachmentFunctional_ne_top N κ Φ hΦ (hs ω) C S hS)

/-- Both source measurability assertions, finite at every outcome of the actual regularised noise. -/
theorem regularised_attachment_measurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ParabolicSpace → ℝ}
    {ε : ℝ} {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (C : RenormalisationConstants) (S : Set ParabolicSpace) (hS : IsCompact S)
    (η : NegExponent) (s : ℝ) :
    (Measurable (fun ω => attachmentFunctional N κ Φ hΦ (ξ ω) C S) ∧
      ∀ ω, attachmentFunctional N κ Φ hΦ (ξ ω) C S < ⊤) ∧
    (Measurable (noiseSlice N η s ξ hξ.1) ∧ ∀ ω, noiseSlice N η s ξ hξ.1 ω < ⊤) :=
  ⟨noiseFunctional_measurable_finite N κ Φ hΦ C S hS ξ hξ.1 (fun z => (hξ.2 z).1),
    noiseSlice_measurable_finite N η s ξ hξ.1 (fun z => (hξ.2 z).1)⟩

end GlobalPhi43.Attachment
