module

public import GlobalPhi43.Proofs.RegularisedAssembly
public import GlobalPhi43.Attachment.RegularisedCoverSupply

@[expose] public noncomputable section
namespace GlobalPhi43
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open Attachment MW20
open scoped ENNReal NNReal

universe u

/-- Uniform regularised-solution bounds with the specified shared profile,
assuming a common deterministic half-cylinder bound. -/
theorem regularisedBound_profile_of_halfCylinderBound
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (Cdef : Kappa → ℝ≥0)
    (hhalf : ∀ κ, MW20HalfCylinderBound κ Φ hΦ (Cdef κ))
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
          prop32ProfileFamily.{u} Φ hΦ Cdef a ρ hρ η p := by
  apply regularisedBound_from_remainder.{u} Φ hΦ Cdef a η hη ρ hρ
  intro Ω ξ hs ε he ω x hx t ht
  let D : RenormalisationConstants := (wickConstant ρ ε+a/3,sunsetConstant ρ ε+0)
  have hD : 3*D.1-9*D.2 = a+3*wickConstant ρ ε-9*sunsetConstant ρ ε := by
    dsimp [D]
    ring
  have hb := start_zero_cover_of_halfCylinderBound Φ hΦ Cdef hhalf 5 (selectedLoss η hη.2)
    (ξ ε ω) (hs ε he ω) D x hx ht
  simpa only [smoothClassicalRemainder,hD,D] using hb

/-- Uniform regularised-solution bounds with the specified profile, obtained from
the deterministic half-cylinder estimate for an admissible kernel. -/
theorem regularisedBound_profile_for_kernel
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
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
          prop32ProfileFamily.{u} Φ hΦ (mw20Constant Φ hΦ) a ρ hρ η p :=
  regularisedBound_profile_of_halfCylinderBound.{u} Φ hΦ (mw20Constant Φ hΦ)
    (mw20Constant_spec Φ hΦ) a η hη ρ hρ

end GlobalPhi43
