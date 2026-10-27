module

public import GlobalPhi43.Flow.ClassicalTranslation
public import GlobalPhi43.Flow.RegularisedSequenceLaw
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import RegularityStructures.Abstract.QFamilyModelBound
public import RegularityStructures.Probability.ModelKolmogorovHSDiagonal
public import Mathlib.Tactic.Linarith
public import GlobalPhi43.Attachment.TranslateIdentification
public import GlobalPhi43.Attachment.RestartCovariance
public import GlobalPhi43.Attachment.FlowCovariance
public import Phi43.Persistence.Instance

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- The already chosen classical solution at every positive regularisation
scale. The unused scales outside (0,1] have the deterministic datum fallback. -/
@[expose] def regularisedClassicalFamily {Ω : Type*} (ρ : ParabolicSpace → ℝ) (mass : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (s : ℝ) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) (ε : ℝ) (ω : Ω) :
    ℝ → C(Torus3, ℝ) := by
  classical
  exact if hε : ε ∈ Ioc (0 : ℝ) 1 then
    smoothSolution (mass + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε)
      (shiftForcing s (ξ ε ω)) (isSmoothOnSpaceTime_shiftForcing (hsmooth ε hε ω) s) x hx
    else fun _ => x

theorem regularisedClassicalFamily_spec {Ω : Type*} (ρ : ParabolicSpace → ℝ) (mass : ℝ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (s : ℝ) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) 1) (ω : Ω) :
    IsClassicalSolution (mass + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε)
      (shiftForcing s (ξ ε ω)) x (regularisedClassicalFamily ρ mass ξ hsmooth s x hx ε ω) := by
  rw [regularisedClassicalFamily, dite_eq_left hε]
  exact smoothSolution_spec _ _ _ x hx

/-- All positive regularisations are driven by the same white noise at the
fixed deterministic shifted start, without a new probability space or event. -/
theorem regularisedFamily_shifted_noise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ParabolicSpace → ℝ}
    {ξ : ℝ → Ω → SpaceTime → ℝ}
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) (s : ℝ) :
    ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P (shiftWhiteNoise W s) ρ ε
      (fun ω => shiftForcing s (ξ ε ω)) := by
  intro ε hε
  exact Attachment.regularisedNoise_time_translate (hξ ε hε) s

end GlobalPhi43.Flow
