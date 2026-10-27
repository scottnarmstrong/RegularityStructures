module

public import GlobalPhi43.Attachment.ReferenceKernel
public import Phi43Statements.RegularisedNoiseExistsUnique

/-! One all-scale regularised noise, chosen before every target exponent. -/

public noncomputable section
namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set

/-- The SAME choice for all eta/kappa targets; only irrelevant scales use zero. -/
@[expose] def referenceNoiseFamily {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) :
    ℝ → Ω → SpaceTime → ℝ := by
  classical
  exact fun ε => if hε : ε ∈ Ioc (0 : ℝ) 1 then
    ((Statements.regularisedNoise_exists_unique P W hW referencePhi0 referencePhi0_isMollifier hε).1).choose
    else fun _ _ => 0

theorem referenceNoiseFamily_spec {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) :
    IsRegularisedNoise P W referencePhi0 ε (referenceNoiseFamily P W hW ε) := by
  classical
  rw [referenceNoiseFamily, dite_eq_left hε]
  exact ((Statements.regularisedNoise_exists_unique P W hW referencePhi0 referencePhi0_isMollifier hε).1).choose_spec

theorem referenceNoiseFamily_smooth {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) 1) (ω : Ω) :
    IsSmoothOnSpaceTime (referenceNoiseFamily P W hW ε ω) :=
  (referenceNoiseFamily_spec P W hW hε).1 ω
end GlobalPhi43.Attachment
