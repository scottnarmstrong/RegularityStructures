/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.ModelPairingGrowth
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Singular `𝒦_γ`: linearity of the model pairing, weighted models

Weighted (`_growth`) version: the global model bounds are replaced by a
`Model.GrowthModel`.

* `pairing_regPi_sum_mul_of_scaled_centres_growth`: `g ↦ ⟨Π_x τ, g⟩` is linear on weighted finite sums of
  scaled test functions with arbitrary centres;
* `pairing_regPi_eq_sum_single_of_scaled_growth`: `⟨Π_z τ, g⟩ = ∑_i τ_i ⟨Π_z e_i, g⟩`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- Linearity of `g ↦ ⟨Π_x τ, g⟩` for finite weighted sums of scaled test functions with
*arbitrary* centres (`τ ∈ T_{<γ}`). -/
theorem pairing_regPi_sum_mul_of_scaled_centres_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    (x : ParabolicSpace) {κ : Type*} (c : κ → ℝ) (g : κ → ParabolicSpace → ℝ) (S : Finset κ)
    (z : κ → ParabolicSpace) (R A : κ → ℝ) (hg : ∀ j ∈ S, IsScaledTest (g j) (z j) (R j) (A j)) :
    parabolicSemigroup.pairing (M.regPi x τ) (fun w => ∑ j ∈ S, c j * g j w) =
      ∑ j ∈ S, c j * parabolicSemigroup.pairing (M.regPi x τ) (g j) := by
  have hΓ : ∀ j, M.gammaMap (z j) x τ ∈ lowerSubspace 𝒯.deg γ := fun j =>
    (M.isGradedUnipotent_gammaMap _ _).map_lowerSubspace hτ
  have e : ∀ j, M.regPi x τ = M.regPi (z j) (M.gammaMap (z j) x τ) := fun j => by
    funext t w; exact (M.regPi_gammaMap _ _ _ _ _).symm
  have ht : ∀ j ∈ S, Tendsto (fun s => ∫ w, M.regPi x τ s w * g j w) (𝓝[>] 0)
      (𝓝 (parabolicSemigroup.pairing (M.regPi x τ) (g j))) := fun j hj => by
    rw [e j]
    exact M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg (hΓ j) (hg j hj)
  have h := parabolicSemigroup.pairing_finset_sum (Λ := M.regPi x τ)
    (fun j w => c j * g j w) S
    (L := fun j => c j * parabolicSemigroup.pairing (M.regPi x τ) (g j))
    (fun j hj => by
      filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
      rw [e j]
      have := (M.integrable_regPi_mul_of_scaled_growth G (hΓ j) (hg j hj) hs.1 hs.2).const_mul
        (c j)
      refine this.congr (Eventually.of_forall fun w => ?_)
      simp only; ring)
    (fun j hj => by
      refine ((ht j hj).const_mul (c j)).congr fun s => ?_
      rw [← integral_const_mul]
      congr 1; funext w; ring)
  have h2 : (fun w => ∑ j ∈ S, c j * g j w) = ∑ j ∈ S, fun w => c j * g j w := by
    funext w; simp [Finset.sum_apply]
  rw [h2, h.2]
  refine Finset.sum_congr rfl fun j hj => ?_
  refine parabolicSemigroup.pairing_eq_of_tendsto ?_
  refine ((ht j hj).const_mul (c j)).congr fun s => ?_
  rw [← integral_const_mul]
  congr 1; funext w; ring

/-- Linearity of `τ ↦ ⟨Π_z τ, g⟩`: `⟨Π_z τ, g⟩ = ∑_i τ_i ⟨Π_z e_i, g⟩` for `τ ∈ T_{<γ}` and `g`
scaled at `z`. -/
theorem pairing_regPi_eq_sum_single_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ} (hg : IsScaledTest g z R A) :
    parabolicSemigroup.pairing (M.regPi z τ) g =
      ∑ i, τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g := by
  set F := Finset.univ.filter (fun i => 𝒯.deg i < γ) with hF
  have hreg : ∀ s w, M.regPi z τ s w = ∑ i ∈ F, τ i * M.regPi z (Pi.single i 1) s w := by
    intro s w
    rw [M.regPi_eq_sum z τ s w, hF, Finset.sum_filter_of_ne]
    intro i _ hne
    by_contra hlt
    exact hne (by rw [(mem_lowerSubspace).1 hτ i (not_lt.1 hlt), zero_mul])
  have hlim : Tendsto (fun s => ∫ y, M.regPi z τ s y * g y) (𝓝[>] 0)
      (𝓝 (∑ i ∈ F, τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)) := by
    have h := tendsto_finsetSum (f := fun i s => τ i * ∫ y, M.regPi z (Pi.single i 1) s y * g y)
      (a := fun i => τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)
      F fun i hi =>
      (M.tendsto_abs_pairing_regPi_single_of_scaled_growth G hdeg
        (Finset.mem_filter.1 hi).2 hg).1.const_mul (τ i)
    refine h.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
    have : (fun y => M.regPi z τ s y * g y) = fun y => ∑ i ∈ F,
        τ i * (M.regPi z (Pi.single i 1) s y * g y) := by
      funext y
      rw [hreg, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, integral_finsetSum _ fun i hi =>
      (M.integrable_regPi_single_mul_of_scaled_growth G (Finset.mem_filter.1 hi).2 hg
        hs.1 hs.2).const_mul _]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  rw [parabolicSemigroup.pairing_eq_of_tendsto hlim, hF, Finset.sum_filter_of_ne]
  intro i _ hne
  by_contra hlt
  exact hne (by rw [(mem_lowerSubspace).1 hτ i (not_lt.1 hlt), zero_mul])

end Model

end RegularityStructures

end
