/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedBphzCauchy
public import Phi43.BPHZ.GModelsStepInputs
public import Phi43.BPHZ.GModelsConstantShift
public import Phi43Statements.Defs.IsModeratePhi43Lift

/-!
# First moments of the `G`-models from the shifted BPHZ models

The `G`-model `Z ε ω` of a lift (`IsModeratePhi43Lift` with constants `C_W + c`, `C_S + c`) has the model
property for the constants `shiftConst N ρ ε (gModelsShift N ρ c ε)`
(`hairerConstants_add_gModelsShift`).  `bphzModels_cauchy_shifted` with `p = 1` therefore gives its
first moments directly, without a Lipschitz bound for the action of the renormalisation constants
on models.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

namespace RegularityStructures.Phi43

/-- A lift of the noise has the model property for the shifted constants. -/
theorem isModeratePhi43ModelOf_shiftConst_of_lift {N : ℕ} {κ : RegularityStructures.Phi43.Kappa}
    {ρ : RegularityStructures.ParabolicSpace → ℝ}
    {c : RegularityStructures.Phi43.RenormalisationConstants} {ε : ℝ}
    {f : RegularityStructures.SpaceTime → ℝ}
    {Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup}
    {ψ : ℝ → C(RegularityStructures.Torus3, ℝ)}
    (h : Statements.IsModeratePhi43Lift N κ f (RegularityStructures.Phi43.wickConstant ρ ε + c.1,
        RegularityStructures.Phi43.sunsetConstant ρ ε + c.2) Z ψ) :
    Statements.IsModeratePhi43ModelOf N κ f (RegularityStructures.Phi43.shiftConst N ρ ε
      (RegularityStructures.Phi43.gModelsShift N ρ c ε)) Z := by
  unfold RegularityStructures.Phi43.shiftConst
  rw [RegularityStructures.Phi43.hairerConstants_add_gModelsShift]
  exact h.2.1

/-- First moments of the `G`-models from the Cauchy bound for the shifted BPHZ models
(`p = 1`). -/
theorem gModels_bphzCauchy_moments (hG1 : RenormalisedCanonicalModelStatement) (hG5 : KolmogorovModelNormStatement.{u, 0})
    (hG7 : NoiseCauchyStatement.{u})
    (hin : ∀ (N : ℕ) (κ : RegularityStructures.Phi43.Kappa),
      RegularityStructures.Phi43.ShiftedBphzInputs.{u} N κ)
    (κ : RegularityStructures.Phi43.Kappa)
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
    (ρ ρ' : RegularityStructures.ParabolicSpace → ℝ)
    (hρ : RegularityStructures.Phi43.IsMollifier ρ)
    (hρ' : RegularityStructures.Phi43.IsMollifier ρ')
    (c : RegularityStructures.Phi43.RenormalisationConstants) {Bc : ℝ}
    (hBc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖RegularityStructures.Phi43.gModelsShift N ρ c ε‖ ≤ Bc)
    (hBc' : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖RegularityStructures.Phi43.gModelsShift N ρ' c ε‖ ≤ Bc)
    (S : Set RegularityStructures.ParabolicSpace) (hS : IsCompact S)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ) (hW : RegularityStructures.IsWhiteNoise P W)
    (ξ ξ' : ℝ → Ω → RegularityStructures.SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε))
    (hξ' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ' ε (ξ' ε))
    (Z Z' : ℝ → Ω → RegularityStructures.Model
      (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup)
    (ψ ψ' : ℝ → Ω → ℝ → C(RegularityStructures.Torus3, ℝ))
    (hlift : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Statements.IsModeratePhi43Lift N κ (ξ ε ω) (RegularityStructures.Phi43.wickConstant ρ ε + c.1,
        RegularityStructures.Phi43.sunsetConstant ρ ε + c.2) (Z ε ω) (ψ ε ω))
    (hlift' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Statements.IsModeratePhi43Lift N κ (ξ' ε ω) (RegularityStructures.Phi43.wickConstant ρ' ε + c.1,
        RegularityStructures.Phi43.sunsetConstant ρ' ε + c.2) (Z' ε ω) (ψ' ε ω)) :
    ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧
      RegularityStructures.SizeMoment P (fun ε ω =>
        (Z ε ω).normOn (RegularityStructures.Phi43.gamma κ) S) C ∧
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ε' ∈ Set.Ioc (0 : ℝ) 1,
        AEMeasurable (fun ω => (Z ε ω).diffNormOn (Z' ε' ω)
          (RegularityStructures.Phi43.gamma κ) S) P ∧
        ∫⁻ ω, (Z ε ω).diffNormOn (Z' ε' ω) (RegularityStructures.Phi43.gamma κ) S ∂P ≤
          ENNReal.ofReal (C * (max ε ε' ^ θ +
            ‖RegularityStructures.Phi43.gModelsShift N ρ c ε -
              RegularityStructures.Phi43.gModelsShift N ρ' c ε'‖)) := by
  obtain ⟨θ, C, hθ, hC, h⟩ := RegularityStructures.Phi43.bphzModels_cauchy_shifted hG1 hG5 hG7
    hin κ hκE N hN ρ ρ' hρ hρ' S hS 1 le_rfl (max Bc 0) (le_max_right _ _)
  refine ⟨θ, C, hθ, hC, fun ε h0 h1 => ?_, fun ε hε ε' hε' => ?_⟩
  · obtain ⟨m1, -, i1, -⟩ := h P W hW ξ ξ' hξ hξ'
      (fun ε => RegularityStructures.Phi43.gModelsShift N ρ c ε)
      (fun ε => RegularityStructures.Phi43.gModelsShift N ρ' c ε)
      (fun ε hε => (hBc ε hε.1 hε.2).trans (le_max_left _ _))
      (fun ε hε => (hBc' ε hε.1 hε.2).trans (le_max_left _ _)) Z Z'
      (fun ε hε => (hlift ε hε).mono fun ω hω => isModeratePhi43ModelOf_shiftConst_of_lift hω)
      (fun ε hε => (hlift' ε hε).mono fun ω hω => isModeratePhi43ModelOf_shiftConst_of_lift hω)
      ε ⟨h0, h1⟩ 1 ⟨one_pos, le_rfl⟩
    exact ⟨m1, by simpa using i1⟩
  · obtain ⟨-, m2, -, i2⟩ := h P W hW ξ ξ' hξ hξ'
      (fun ε => RegularityStructures.Phi43.gModelsShift N ρ c ε)
      (fun ε => RegularityStructures.Phi43.gModelsShift N ρ' c ε)
      (fun ε hε => (hBc ε hε.1 hε.2).trans (le_max_left _ _))
      (fun ε hε => (hBc' ε hε.1 hε.2).trans (le_max_left _ _)) Z Z'
      (fun ε hε => (hlift ε hε).mono fun ω hω => isModeratePhi43ModelOf_shiftConst_of_lift hω)
      (fun ε hε => (hlift' ε hε).mono fun ω hω => isModeratePhi43ModelOf_shiftConst_of_lift hω)
      ε hε ε' hε'
    exact ⟨m2, by simpa using i2⟩

end RegularityStructures.Phi43

end
