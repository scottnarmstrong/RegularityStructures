module

public import GlobalPhi43.Attachment.RegularisedNoiseLaw
public import GlobalPhi43.Attachment.GrowthEvent

/-! A common measurable space for the deterministic canonical constructions. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43

/-- Smooth noises with polynomial derivative growth and the coordinate sigma algebra. -/
abbrev SmoothGrowingNoise := {f : SpaceTime → ℝ //
  IsSmoothOnSpaceTime f ∧ Statements.HasPhi43NoiseGrowth f}

/-- Set the noise to zero off its exact growth event. -/
def growingNoise {Ω : Type*} (ξ : Ω → SpaceTime → ℝ)
    (hξ : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (ω : Ω) : SmoothGrowingNoise := by
  classical
  exact if hg : Statements.HasPhi43NoiseGrowth (ξ ω) then ⟨ξ ω, hξ ω, hg⟩
    else ⟨0, contDiff_const, hasPhi43NoiseGrowth_zero⟩

/-- Equality of laws in a subtype with the induced sigma algebra follows from equality
of the underlying laws, even when the subtype is not assumed measurable in the ambient space. -/
theorem subtype_map_eq_of_val_map_eq {A Ω Ω' : Type*} [MeasurableSpace A]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {s : Set A}
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → s} {Y : Ω' → s}
    (h : P.map (fun ω => (X ω).1) = P'.map (fun ω => (Y ω).1))
    (hX : Measurable X) (hY : Measurable Y) : P.map X = P'.map Y := by
  apply Measure.ext
  intro u hu
  obtain ⟨v, hv, he⟩ := MeasurableSpace.measurableSet_comap.mp hu
  have hm : (P.map X).map Subtype.val = (P'.map Y).map Subtype.val := by
    rw [Measure.map_map measurable_subtype_coe hX, Measure.map_map measurable_subtype_coe hY]
    exact h
  have hh := congrArg (fun μ : Measure A => μ v) hm
  rw [Measure.map_apply measurable_subtype_coe hv, Measure.map_apply measurable_subtype_coe hv] at hh
  simpa only [he] using hh

end GlobalPhi43.Attachment
