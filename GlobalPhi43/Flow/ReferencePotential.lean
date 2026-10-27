module

public import GlobalPhi43.Flow.WindowAttached
public import GlobalPhi43.Attachment.PotentialObservable

@[expose] public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- The same exact growth-event fallback as the attached model, for the whole reference family. -/
def referenceGrowingNoise {Ω : Type*} (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ε : ℝ) (ω : Ω) : Attachment.SmoothGrowingNoise := by
  classical
  exact if hε : ε ∈ Ioc (0 : ℝ) 1 then Attachment.growingNoise (ξ ε) (hsmooth ε hε) ω
    else ⟨0, contDiff_const, hasPhi43NoiseGrowth_zero⟩

/-- One fixed potential representative, chosen from the actual smooth growing forcing. -/
def referencePotential {Ω : Type*} (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (ε : ℝ) (ω : Ω) : ℝ → C(Torus3, ℝ) :=
  Attachment.noisePotential (referenceGrowingNoise ξ hsmooth ε ω)

/-- On the literal growth event the corrected forcing is the original forcing. -/
theorem referenceGrowingNoise_eq {Ω : Type*} (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) {ω : Ω}
    (hω : ω ∈ Attachment.growthEvent (ξ ε)) :
    (referenceGrowingNoise ξ hsmooth ε ω).val = ξ ε ω := by
  classical
  change Statements.HasPhi43NoiseGrowth (ξ ε ω) at hω
  simp only [referenceGrowingNoise, dite_eq_left hε, Attachment.growingNoise, dite_eq_left hω]

/-- The potential specification is pointwise on the exact growth event. -/
theorem referencePotential_spec {Ω : Type*} (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) {ω : Ω}
    (hω : ω ∈ Attachment.growthEvent (ξ ε)) :
    IsMassivePotential (ξ ε ω) (referencePotential ξ hsmooth ε ω) := by
  have h := (Attachment.noisePotential_spec (referenceGrowingNoise ξ hsmooth ε ω)).1
  rw [referenceGrowingNoise_eq ξ hsmooth hε hω] at h
  exact h

/-- The a.e. potential premise is derived from the actual regularised-noise growth theorem. -/
theorem referencePotential_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, IsMassivePotential (ξ ε ω)
      (referencePotential ξ (fun ε hε => (hξ ε hε).1) ε ω) := by
  obtain ⟨hm, hp⟩ := Attachment.growthEvent_measurable_measure_one P W hW ρ hρ hε
    (ξ ε) (hξ ε hε)
  have hfull : ∀ᵐ ω ∂P, ω ∈ Attachment.growthEvent (ξ ε) :=
    (mem_ae_iff_prob_eq_one hm).mpr hp
  exact hfull.mono fun _ hω => referencePotential_spec ξ _ hε hω

end GlobalPhi43.Flow
