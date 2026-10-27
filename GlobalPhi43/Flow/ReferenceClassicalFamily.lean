module

public import GlobalPhi43.Attachment.ReferenceNoiseFamily
public import GlobalPhi43.Flow.FullRegularisedSolutions

/-! A total reference classical family with no smoothness-proof argument. -/

public noncomputable section
namespace GlobalPhi43.Flow
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set
open GlobalPhi43.Attachment

/-- Total at every scale and datum. The used smooth-data branch is the
existing chosen classical solution, with the common physical drift. -/
@[expose] def referenceClassicalFamily {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) (a : ℝ) :
    ℝ → C(Torus3,ℝ) → Ω → ℝ → C(Torus3,ℝ) := by
  classical
  exact fun ε x ω => if hε : ε ∈ Ioc (0 : ℝ) 1 then
    if hx : IsSmoothOnTorus x then
      smoothSolution (a + 3 * wickConstant referencePhi0 ε - 9 * sunsetConstant referencePhi0 ε)
        (referenceNoiseFamily P W hW ε ω) (referenceNoiseFamily_smooth P W hW ε hε ω) x hx
    else fun _ => x
  else fun _ => x

theorem referenceClassicalFamily_spec {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) (a : ℝ)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1)
    (x : C(Torus3,ℝ)) (hx : IsSmoothOnTorus x) (ω : Ω) :
    IsClassicalSolution (a + 3 * wickConstant referencePhi0 ε - 9 * sunsetConstant referencePhi0 ε)
      (referenceNoiseFamily P W hW ε ω) x (referenceClassicalFamily P W hW a ε x ω) := by
  classical
  rw [referenceClassicalFamily, dite_eq_left hε, dite_eq_left hx]
  exact smoothSolution_spec _ _ _ x hx

end GlobalPhi43.Flow
