module

public import GlobalPhi43.Proofs.RegularisedDomination

/-! Uniform regularised-solution bounds for a fixed profile, assuming a
pointwise physical-cover estimate for the remainder. -/

@[expose] public noncomputable section
namespace GlobalPhi43
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open Attachment MW20
open scoped NNReal ENNReal

universe u

/-- Assemble every clause for arbitrary supplied classical solution families.
One literal sourceMajorant precedes all scales, outcomes, data, times and p. -/
theorem regularisedBound_from_remainder (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (Cdef : Kappa → ℝ≥0) (a η : ℝ) (hη : η ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)))
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    (hcover : ∀ {Ω : Type u} (ξ : ℝ → Ω → SpaceTime → ℝ)
      (hs : ∀ ε ∈ Ioc (0:ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
      (ε : ℝ) (he : ε ∈ Ioc (0:ℝ) 1) (ω : Ω) (x : C(Torus3,ℝ))
      (hx : IsSmoothOnTorus x) (t : ℝ) (_ht : t ∈ Ioc (0:ℝ) 1),
      ENNReal.ofReal (Real.sqrt t) *
        ‖Flow.smoothSolution (a+3*wickConstant ρ ε-9*sunsetConstant ρ ε)
          (ξ ε ω) (hs ε he ω) x hx t - smoothNoiseJ 5 ⟨ξ ε ω,hs ε he ω⟩ t‖ₑ ≤
      2*(Cdef (selectedLoss η hη.2):ENNReal)*max 2
        (attachmentFunctional 5 (selectedLoss η hη.2) Φ hΦ (ξ ε ω)
          (wickConstant ρ ε+a/3,sunsetConstant ρ ε+0) (Flow.coverRegion 0))) :
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
  intro Ω _ P _ W hW ξ hξ uε hu
  let κ := selectedLoss η hη.2
  let hs := fun ε hε => (hξ ε hε).1
  let M := sourceMajorant κ Φ hΦ ρ a (Cdef κ) ξ hs
  have hprofile := prop32Profile_spec.{u} Φ hΦ Cdef a η hη.2 ρ hρ P W hW ξ hξ
  refine ⟨M,fun ε _ => hprofile.1 ε,?_,?_⟩
  · intro ε he ω x hx t ht
    have horder : η ≤ (Flow.lossExponent κ : ℝ) := by
      have hh := (selectedLoss_spec η hη.2).2
      change η ≤ -(1/2:ℝ)-κ.1
      dsimp only [κ]
      linarith
    exact sourceMajorant_dominates_classical_of_remainder κ Φ hΦ ρ a (Cdef κ) ξ hs he ω
      x hx (uε ε x ω) (hu ε he x hx ω) ht horder (hcover ξ hs ε he ω x hx t ht)
  · intro p hp
    rw [prop32ProfileFamily_eq Φ hΦ Cdef a ρ hρ hη]
    exact hprofile.2 p hp

end GlobalPhi43
