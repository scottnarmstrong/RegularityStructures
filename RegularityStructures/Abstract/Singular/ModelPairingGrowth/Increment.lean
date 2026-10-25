/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Pairing
public import RegularityStructures.Abstract.Singular.ModelPairing.Increment
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Weighted linearity and increments of the model pairing with scaled test functions

Weighted versions of the items of `RegularityStructures.Abstract.Singular.ModelPairing.Increment`:
additivity of `g ↦ ⟨Π_z τ, g⟩` over finite families of scaled test functions at `z`, additivity in
`τ ∈ T_{<γ}`, and the increment bound

  `|⟨Π_z τ, g⟩ - ⟨Π_y τ', g⟩| ≤ c max(1, C_Γ) C_Π (ρΠ(z) ρΓ(z)) (A R⁵)
      ∑_i |(τ - Γ_{zy} τ')_i| R^{deg i}`

for `g` scaled at `z`, the weight being evaluated at the base point `z`. The transport identity
`Model.pairing_regPi_eq_gammaMap` involves no bounds and is reused as is.

Source: [Hai14] = arXiv:1303.5113v4, (2.15), Proposition 7.2; [Hos25] = arXiv:2310.07396v2.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
  {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ}

/-- Additivity of the pairing in the test function, for scaled test functions at the same `z`
(weighted setting). -/
theorem pairing_regPi_finset_sum_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {κ : Type*} (g : κ → ParabolicSpace → ℝ) (S : Finset κ) (R A : κ → ℝ)
    (hg : ∀ j ∈ S, IsScaledTest (g j) z (R j) (A j)) :
    parabolicSemigroup.pairing (M.regPi z τ) (∑ j ∈ S, g j) =
      ∑ j ∈ S, parabolicSemigroup.pairing (M.regPi z τ) (g j) :=
  (parabolicSemigroup.pairing_finset_sum g S
    (fun j hj => by
      filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
      exact M.integrable_regPi_mul_of_scaled_growth G hτ (hg j hj) hs.1 hs.2)
    (fun j hj => M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg hτ (hg j hj))).2

/-- Additivity of the pairing in `τ ∈ T_{<γ}` (weighted setting). -/
theorem pairing_regPi_sub_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ₁ τ₂ : ι → ℝ}
    (h₁ : τ₁ ∈ lowerSubspace 𝒯.deg γ) (h₂ : τ₂ ∈ lowerSubspace 𝒯.deg γ)
    (hg : IsScaledTest g z R A) :
    parabolicSemigroup.pairing (M.regPi z (τ₁ - τ₂)) g =
      parabolicSemigroup.pairing (M.regPi z τ₁) g - parabolicSemigroup.pairing (M.regPi z τ₂) g := by
  have t₁ := M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg h₁ hg
  have t₂ := M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg h₂ hg
  have t₃ := M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg (Submodule.sub_mem _ h₁ h₂) hg
  have t₄ := t₁.sub t₂
  refine tendsto_nhds_unique t₃ (t₄.congr' ?_)
  filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
  rw [← integral_sub (M.integrable_regPi_mul_of_scaled_growth G h₁ hg hs.1 hs.2)
    (M.integrable_regPi_mul_of_scaled_growth G h₂ hg hs.1 hs.2)]
  congr 1; funext y
  rw [M.regPi_sub, sub_mul]

end Model

end RegularityStructures

end
