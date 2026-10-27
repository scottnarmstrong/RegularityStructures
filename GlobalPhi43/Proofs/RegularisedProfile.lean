module

public import GlobalPhi43.Attachment.SourceMajorantProfile

@[expose] public noncomputable section

namespace GlobalPhi43
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open Attachment MW20
open scoped NNReal ENNReal

universe u

/-- One deterministic target profile, selected before any source probability space.
The MW coefficient is the one at the very same selected construction loss. -/
def prop32Profile (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (Cdef : Kappa → ℝ≥0) (a η : ℝ) (hη : η < -(1/2:ℝ))
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) : ℝ → ℝ≥0 :=
  Classical.choose (selected_sourceMajorant_profile.{u} η hη Φ hΦ ρ hρ a Cdef).2

/-- Shared total profile family. Only admissible targets select
construction losses; off-range values are the fixed zero profile. -/
def prop32ProfileFamily (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (Cdef : Kappa → ℝ≥0) (a : ℝ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    (η : ℝ) : ℝ → ℝ≥0 := by
  classical
  exact if hη : η ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ)) then
    prop32Profile.{u} Φ hΦ Cdef a η hη.2 ρ hρ else fun _ => 0

theorem prop32ProfileFamily_eq (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (Cdef : Kappa → ℝ≥0) (a : ℝ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {η : ℝ} (hη : η ∈ Ioo (-(2/3:ℝ)) (-(1/2:ℝ))) :
    prop32ProfileFamily.{u} Φ hΦ Cdef a ρ hρ η = prop32Profile.{u} Φ hΦ Cdef a η hη.2 ρ hρ := by
  rw [prop32ProfileFamily,dite_eq_left hη]

/-- The literal everywhere-defined majorant and its single before-space profile. -/
theorem prop32Profile_spec (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (Cdef : Kappa → ℝ≥0) (a η : ℝ) (hη : η < -(1/2:ℝ))
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0:ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) :
    let κ := selectedLoss η hη
    let M := sourceMajorant κ Φ hΦ ρ a (Cdef κ) ξ (fun ε hε => (hξ ε hε).1)
    (∀ ε, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω) ∧
    ∀ p : ℝ, 1 ≤ p →
      (⨆ ε ∈ Ioc (0:ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω)^p ∂P) ≤
        prop32Profile.{u} Φ hΦ Cdef a η hη ρ hρ p :=
  Classical.choose_spec (selected_sourceMajorant_profile.{u} η hη Φ hΦ ρ hρ a Cdef).2
    P W hW ξ hξ

end GlobalPhi43
