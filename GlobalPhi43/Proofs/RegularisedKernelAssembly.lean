module

public import GlobalPhi43.Proofs.KernelRegularisedProfile
public import GlobalPhi43.Proofs.RegularisedHalfCylinderAssembly

/-! Uniform regularised-solution bounds for the specified profile.
The kernel and deterministic half-cylinder coefficient are fixed. -/

@[expose] public noncomputable section
namespace GlobalPhi43
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open Attachment MW20
open scoped ENNReal NNReal

universe u

/-- Uniform bounds with the canonical deterministic profile, using the fixed kernel,
half-cylinder coefficient, majorant, moment estimates and physical cover. -/
theorem regularisedBound_profile
    (a η : ℝ) (hη : η ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)))
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W)
      (ξ : ℝ → Ω → SpaceTime → ℝ)
      (_hξ : ∀ ε ∈ Ioc (0:ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
      (uε : ℝ → C(Torus3,ℝ) → Ω → ℝ → C(Torus3,ℝ))
      (_hu : ∀ ε ∈ Ioc (0:ℝ) 1, ∀ x : C(Torus3,ℝ), IsSmoothOnTorus x → ∀ ω,
        IsClassicalSolution (a+3*wickConstant ρ ε-9*sunsetConstant ρ ε) (ξ ε ω) x (uε ε x ω)),
    ∃ M : ℝ → Ω → ℝ,
      (∀ ε ∈ Ioc (0:ℝ) 1, Measurable (M ε) ∧ ∀ ω, 0≤M ε ω) ∧
      (∀ ε ∈ Ioc (0:ℝ) 1, ∀ ω, ∀ x : C(Torus3,ℝ), IsSmoothOnTorus x →
        ∀ t ∈ Ioc (0:ℝ) 1,
        ENNReal.ofReal (Real.sqrt t)*holderBesovENorm η (uε ε x ω t) ≤ ENNReal.ofReal (M ε ω)) ∧
      ∀ p : ℝ, 1≤p →
        (⨆ ε ∈ Ioc (0:ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω)^p ∂P) ≤
          regularisedProfile.{u} a η ρ hρ p :=
  regularisedBound_profile_for_kernel.{u} referencePhi0 referencePhi0_kernelProfile a η hη ρ hρ

end GlobalPhi43
