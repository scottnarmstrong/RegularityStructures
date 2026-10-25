/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.StepStatements
public import RegularityStructures.BPHZ.CauchyMoment
public import Phi43.BPHZ.GModelsShiftLimit

/-!
# The inputs of the convergence of the G-models

From the Cauchy property of the BPHZ models (moments of the `K`-models), the Cauchy property of
the noises (moments of the noise) and the comparison of the renormalisation constants (convergence
of the constant differences) we extract the first-moment bounds (`SizeMoment`, `MomentBound`), the
bound on the constant shifts and the convergence of their differences, in the forms consumed by
`gModels_tight`, `gModels_cauchy` and `gModels_dyadic_of_shiftRate`.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

namespace RegularityStructures.Phi43

/-- From the comparison of the renormalisation constants: the shifts are bounded on `(0, 1]` and
asymptotically equal across mollifiers. -/
theorem gModels_constants (hG8 : ConstantsComparisonStatement) (N : ℕ)
    {ρ ρ' : RegularityStructures.ParabolicSpace → ℝ}
    (hρ : RegularityStructures.Phi43.IsMollifier ρ)
    (hρ' : RegularityStructures.Phi43.IsMollifier ρ')
    (c : RegularityStructures.Phi43.RenormalisationConstants) :
    ∃ Bc : ℝ,
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖RegularityStructures.Phi43.gModelsShift N ρ c ε‖ ≤ Bc) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖RegularityStructures.Phi43.gModelsShift N ρ' c ε‖ ≤ Bc) ∧
      Tendsto (fun e : ℝ × ℝ => ‖RegularityStructures.Phi43.gModelsShift N ρ c e.1 -
          RegularityStructures.Phi43.gModelsShift N ρ' c e.2‖)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun e : ℝ × ℝ => ‖RegularityStructures.Phi43.gModelsShift N ρ c e.1 -
          RegularityStructures.Phi43.gModelsShift N ρ c e.2‖)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨L₁, L₂, _, hL⟩ := hG8 N
  obtain ⟨h1, h2, -⟩ := hL ρ hρ
  obtain ⟨h1', h2', -⟩ := hL ρ' hρ'
  obtain ⟨B, hB⟩ := RegularityStructures.Phi43.exists_norm_gModelsShift_le N ρ hρ c h1 h2
  obtain ⟨B', hB'⟩ := RegularityStructures.Phi43.exists_norm_gModelsShift_le N ρ' hρ' c h1' h2'
  exact ⟨max B B', fun ε h0 h1 => (hB ε h0 h1).trans (le_max_left _ _),
    fun ε h0 h1 => (hB' ε h0 h1).trans (le_max_right _ _),
    RegularityStructures.Phi43.tendsto_norm_gModelsShift_sub N ρ ρ' c h1 h2 h1' h2',
    RegularityStructures.Phi43.tendsto_norm_gModelsShift_sub N ρ ρ c h1 h2 h1 h2⟩

/-- From the Cauchy property of the noises with `p = 1`: first-moment bounds for the noise sizes and
distances. -/
theorem gModels_noiseCauchy_moments (hG7 : NoiseCauchyStatement.{u}) (η : RegularityStructures.NegExponent)
    (hη : (η : ℝ) < -(1 / 2 : ℝ)) (ρ ρ' : RegularityStructures.ParabolicSpace → ℝ)
    (hρ : RegularityStructures.Phi43.IsMollifier ρ)
    (hρ' : RegularityStructures.Phi43.IsMollifier ρ') (T : ℝ) (hT : 1 ≤ T)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ) (hW : RegularityStructures.IsWhiteNoise P W)
    (ξ ξ' : ℝ → Ω → RegularityStructures.SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε))
    (hξ' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ' ε (ξ' ε))
    (ψ ψ' : ℝ → Ω → ℝ → C(RegularityStructures.Torus3, ℝ))
    (hψ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω))
    (hψ' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P, RegularityStructures.IsMassivePotential (ξ' ε ω) (ψ' ε ω)) :
    ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧
      RegularityStructures.SizeMoment P (fun ε ω => Statements.phi43NoiseSize η T (ψ ε ω)) C ∧
      RegularityStructures.MomentBound P (fun ε ε' ω =>
        Statements.phi43NoiseDist η T (ψ ε ω) (ψ' ε' ω)) θ C := by
  obtain ⟨-, -, β₀, hβ, h⟩ := hG7 η hη
  obtain ⟨C, hC, hh⟩ := h ρ ρ' hρ hρ' T hT 1 le_rfl
  refine ⟨β₀, C, hβ, hC, fun ε h0 h1 => ?_, fun ε ε' h0 h1 h0' h1' => ?_⟩
  · obtain ⟨m1, -, i1, -⟩ := hh P W hW ξ ξ' hξ hξ' ψ ψ' hψ hψ' ε ⟨h0, h1⟩ 1 ⟨one_pos, le_rfl⟩
    exact ⟨m1, by simpa using i1⟩
  · obtain ⟨-, m2, -, i2⟩ := hh P W hW ξ ξ' hξ hξ' ψ ψ' hψ hψ' ε ⟨h0, h1⟩ ε' ⟨h0', h1'⟩
    exact ⟨m2, by simpa using i2⟩

end RegularityStructures.Phi43

end
