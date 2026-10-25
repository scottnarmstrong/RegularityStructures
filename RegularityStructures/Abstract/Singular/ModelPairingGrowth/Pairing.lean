/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Single
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Weighted model pairing with scaled test functions

Weighted versions of `Model.tendsto_integral_regPi_mul_of_scaled` and
`Model.abs_pairing_regPi_le_of_scaled`: for `M.GrowthModel γ CPi CGam ρP ρG p qG`, `τ ∈ T_{<γ}`
and `g` scaled at `z` (`IsScaledTest g z R A`),

  `|⟨Π_z τ, g⟩| ≤ c max(1, C_Γ) C_Π (ρΠ(z) ρΓ(z)) (A R⁵) ∑_i |τ_i| R^{deg i}`,

`c = r4ModelConstGrowth 𝒯 p qG γ`. The weight is evaluated at the base point `z`.

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

private theorem regPi_eq_sum_lower_growth (M : Model 𝒯 parabolicSemigroup) {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (x : ParabolicSpace) (s : ℝ) (y : ParabolicSpace) :
    M.regPi x τ s y = ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      τ i * M.regPi x (Pi.single i 1) s y := by
  rw [M.regPi_eq_sum x τ s y, Finset.sum_filter_of_ne]
  intro i _ hne
  by_contra h
  exact hne (by rw [(mem_lowerSubspace).1 hτ i (not_lt.1 h), zero_mul])

private theorem regPi_mul_eq_sum_growth (M : Model 𝒯 parabolicSemigroup) {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (g : ParabolicSpace → ℝ) (x : ParabolicSpace) (s : ℝ) :
    (fun y => M.regPi x τ s y * g y) = fun y => ∑ i ∈ Finset.univ.filter
      (fun i => 𝒯.deg i < γ), τ i * (M.regPi x (Pi.single i 1) s y * g y) := by
  funext y
  rw [regPi_eq_sum_lower_growth M hτ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- For `0 < s ≤ 1`, `y ↦ (Q_s Π_z τ)(y) g(y)` is integrable (`τ ∈ T_{<γ}`, weighted setting). -/
theorem integrable_regPi_mul_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (hg : IsScaledTest g z R A) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) : Integrable (fun y => M.regPi z τ s y * g y) := by
  rw [regPi_mul_eq_sum_growth M hτ]
  exact integrable_finsetSum _ fun i hi =>
    (M.integrable_regPi_single_mul_of_scaled_growth G (Finset.mem_filter.1 hi).2 hg hs
      hs1).const_mul _

private theorem tendsto_integral_regPi_mul_sum_growth
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (hg : IsScaledTest g z R A) :
    Tendsto (fun s => ∫ y, M.regPi z τ s y * g y) (𝓝[>] 0)
      (𝓝 (∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
        τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)) := by
  set F := Finset.univ.filter (fun i => 𝒯.deg i < γ) with hF
  have h := tendsto_finsetSum (f := fun i s => τ i * ∫ y, M.regPi z (Pi.single i 1) s y * g y)
    (a := fun i => τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)
    F fun i hi =>
    (M.tendsto_abs_pairing_regPi_single_of_scaled_growth G hdeg
      (Finset.mem_filter.1 hi).2 hg).1.const_mul (τ i)
  refine h.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
  rw [regPi_mul_eq_sum_growth M hτ, integral_finsetSum _ fun i hi =>
    (M.integrable_regPi_single_mul_of_scaled_growth G (Finset.mem_filter.1 hi).2 hg
      hs.1 hs.2).const_mul _]
  exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm

/-- Convergence of the regularised pairings of `Π_z τ` with a scaled test function
(weighted setting). -/
theorem tendsto_integral_regPi_mul_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    (hg : IsScaledTest g z R A) :
    Tendsto (fun s => ∫ y, M.regPi z τ s y * g y) (𝓝[>] 0)
      (𝓝 (parabolicSemigroup.pairing (M.regPi z τ) g)) := by
  have hlim := tendsto_integral_regPi_mul_sum_growth G hdeg hτ hg
  rwa [parabolicSemigroup.pairing_eq_of_tendsto hlim]

end Model

end RegularityStructures

end
