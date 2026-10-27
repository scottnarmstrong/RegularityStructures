module

public import GlobalPhi43.Attachment.SliceRadiusFour
public import GlobalPhi43.Attachment.SmoothNoiseSliceLaw

/-! Deterministic specialization to the existing source time-slice observables.
These are the unchanged everywhere-defined observables; growth is a hypothesis
of the bound, not an event-dependent change to the random variable. -/

@[expose] public noncomputable section
namespace GlobalPhi43.Attachment
open Set RegularityStructures RegularityStructures.Phi43

/-- The actual smooth-noise slice observable has the radius-four bound.
The coefficient is chosen before the smooth noise and its lift data. -/
theorem smoothNoiseSlice_bound (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ, 0<c ∧ ∀ (f : SmoothNoise) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.HasPhi43NoiseGrowth f.1 →
      Statements.IsModeratePhi43ModelOf N κ f.1 C Z →
      ∀ (ψ : ℝ → C(Torus3,ℝ)), IsMassivePotential f.1 ψ → ∀ s : ℝ,
      smoothNoiseSlice N (Flow.lossExponent κ) s f ≤
      ENNReal.ofReal c * (Flow.unitPotentialSize (Flow.lossExponent κ) s ψ +
        (1+Z.normOn (gamma κ) (radiusFourRegion (Flow.sliceRegion s)))^3) := by
  obtain ⟨c,hc,h⟩ := slice_radius_four N κ
  refine ⟨c,hc,?_⟩
  intro f C Z hg hZ ψ hψ s
  unfold smoothNoiseSlice
  apply iSup_le
  intro t
  exact h f.1 C Z f.2 hg hZ ψ hψ s t.val t.property

/-- Pointwise bound for the regularised-noise family. No probability space, growth event, or
outcome-dependent coefficient is chosen to define the actual observable. -/
theorem noiseSlice_bound (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ, 0<c ∧ ∀ {Ω : Type*} (ξ : Ω → SpaceTime → ℝ)
      (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (ω : Ω) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.HasPhi43NoiseGrowth (ξ ω) →
      Statements.IsModeratePhi43ModelOf N κ (ξ ω) C Z →
      ∀ (ψ : ℝ → C(Torus3,ℝ)), IsMassivePotential (ξ ω) ψ → ∀ s : ℝ,
      noiseSlice N (Flow.lossExponent κ) s ξ hs ω ≤
      ENNReal.ofReal c * (Flow.unitPotentialSize (Flow.lossExponent κ) s ψ +
        (1+Z.normOn (gamma κ) (radiusFourRegion (Flow.sliceRegion s)))^3) := by
  obtain ⟨c,hc,h⟩ := smoothNoiseSlice_bound N κ
  refine ⟨c,hc,?_⟩
  intro Ω ξ hs ω C Z hg hZ ψ hψ s
  exact h (asSmoothNoise ξ hs ω) C Z hg hZ ψ hψ s

end GlobalPhi43.Attachment
