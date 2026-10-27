module

public import GlobalPhi43.Attachment.SmoothNoiseSlices

/-! Space-independent laws of actual J time slices, everywhere on the full smooth-noise space.
This evaluation-sigma-algebra result does not assert the separate C-infinity Polish topology. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43 Set

/-- Bundle a pathwise smooth noise without changing its value at any outcome. -/
def asSmoothNoise {Ω : Type*} (ξ : Ω → SpaceTime → ℝ)
    (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (ω : Ω) : SmoothNoise := ⟨ξ ω, hs ω⟩

theorem asSmoothNoise_measurable {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Ω → SpaceTime → ℝ) (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω))
    (hm : ∀ z, Measurable fun ω => ξ ω z) : Measurable (asSmoothNoise ξ hs) :=
  (measurable_pi_iff.mpr hm).subtype_mk

/-- The actual J time-slice function on any pathwise smooth family. -/
def noiseSlice {Ω : Type*} (N : ℕ) (η : NegExponent) (s : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (ω : Ω) : ENNReal :=
  smoothNoiseSlice N η s (asSmoothNoise ξ hs ω)

/-- The common observable represents the literal source quantity at every outcome. -/
theorem noiseSlice_eq {Ω : Type*} (N : ℕ) (η : NegExponent) (s : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (ω : Ω) :
    noiseSlice N η s ξ hs ω = ⨆ t : Ioc (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt t.1) * holderBesovENorm η
        ⟨fun x => treeJ N (ξ ω) (s + t.1, x),
          (continuous_treeJ (hs ω)).comp (continuous_const.prodMk continuous_id)⟩ := rfl

/-- Measurability and finiteness of the actual weighted J slice, everywhere in the noise space. -/
theorem noiseSlice_measurable_finite {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ) (η : NegExponent) (s : ℝ) (ξ : Ω → SpaceTime → ℝ)
    (hs : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (hm : ∀ z, Measurable fun ω => ξ ω z) :
    Measurable (noiseSlice N η s ξ hs) ∧ ∀ ω, noiseSlice N η s ξ hs ω < ⊤ :=
  ⟨(smoothNoiseSlice_measurable N η s).comp (asSmoothNoise_measurable ξ hs hm),
    fun ω => smoothNoiseSlice_lt_top N η s (asSmoothNoise ξ hs ω)⟩

end GlobalPhi43.Attachment
