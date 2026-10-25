/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.WindowAt.ScaledNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Window pairing of `Π_z τ` with scaled test functions, near-pair `Γ`-bounds

For `τ ∈ T_{<γ}` and `g` scaled at `z` with radius `R` and constant `A`, with `PiBoundOn` and
`GammaNearOn` on `hairerTimeWindow` and qualitative growth, the regularised pairings converge
(`tendsto_integral_regPi_mul_of_scaled_onWindowAt_near`) and satisfy the window form of the model
bound (2.15), `|⟨Π_z τ, g⟩| ≤ r4ModelConst 𝒯 γ · max(1, C_Γ) C_Π · (A R⁵) ∑_i |τ_i| R^{deg i}`
(`abs_pairing_regPi_le_of_scaled_onWindowAt_near`). The constant `r4ModelConst 𝒯 γ` does not depend
on the growth constants.

These statements are for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

open scoped Topology

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ} {g : ParabolicSpace → ℝ}
  {z : ParabolicSpace} {R A : ℝ}

private theorem regPi_eq_sum_lower_onWindowAt {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    (x : ParabolicSpace) (s : ℝ) (y : ParabolicSpace) :
    M.regPi x τ s y = ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      τ i * M.regPi x (Pi.single i 1) s y := by
  rw [M.regPi_eq_sum x τ s y, Finset.sum_filter_of_ne]
  intro i _ hne
  by_contra h
  exact hne (by rw [(mem_lowerSubspace).1 hτ i (not_lt.1 h), zero_mul])

private theorem tendsto_integral_regPi_mul_sum_onWindowAt
    (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hgrowth : M.HasQualitativeGrowthAt γ z)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hball : ∀ y, parabolicNorm (y - z) ≤ 1 → y ∈ hairerTimeWindow) {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (hg : IsScaledTest g z R A) :
    Tendsto (fun s => ∫ y, M.regPi z τ s y * g y) (𝓝[>] 0)
      (𝓝 (∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
        τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)) := by
  set F := Finset.univ.filter (fun i => 𝒯.deg i < γ) with hF
  have h := tendsto_finsetSum (f := fun i s => τ i * ∫ y, M.regPi z (Pi.single i 1) s y * g y)
    (a := fun i => τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)
    F fun i hi =>
    (M.tendsto_abs_pairing_regPi_single_of_scaled_onWindowAt_near hPi hCPi hGam hgrowth hdeg
      (Finset.mem_filter.1 hi).2 hball hg).1.const_mul (τ i)
  refine h.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
  have : (fun y => M.regPi z τ s y * g y) = fun y => ∑ i ∈ F,
      τ i * (M.regPi z (Pi.single i 1) s y * g y) := by
    funext y
    rw [M.regPi_eq_sum_lower_onWindowAt hτ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, integral_finsetSum _ fun i hi =>
    (M.integrable_regPi_single_mul_of_scaled_onWindowAt_near hPi hCPi hGam (Finset.mem_filter.1 hi).2
      hball hg hs.1 hs.2).const_mul _]
  exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm

/-- Convergence of the regularised pairings of `Π_z τ` with a scaled test function (window). -/
theorem tendsto_integral_regPi_mul_of_scaled_onWindowAt_near
    (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hgrowth : M.HasQualitativeGrowthAt γ z)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hball : ∀ y, parabolicNorm (y - z) ≤ 1 → y ∈ hairerTimeWindow) {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (hg : IsScaledTest g z R A) :
    Tendsto (fun s => ∫ y, M.regPi z τ s y * g y) (𝓝[>] 0)
      (𝓝 (parabolicSemigroup.pairing (M.regPi z τ) g)) := by
  have hlim := M.tendsto_integral_regPi_mul_sum_onWindowAt hPi hCPi hGam hgrowth hdeg hball hτ hg
  rwa [parabolicSemigroup.pairing_eq_of_tendsto hlim]

/-- **Window model bound (2.15)** for `⟨Π_z τ, g⟩`, `τ ∈ T_{<γ}`, `g` scaled at `z`, with the
constant `r4ModelConst 𝒯 γ · max(1, C_Γ) C_Π` independent of the growth constants. -/
theorem abs_pairing_regPi_le_of_scaled_onWindowAt_near (hPi : M.PiBoundOn γ CPi hairerTimeWindow)
    (hCPi : 0 ≤ CPi) (hGam : M.GammaNearOn γ CGam hairerTimeWindow)
    (hgrowth : M.HasQualitativeGrowthAt γ z) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hball : ∀ y, parabolicNorm (y - z) ≤ 1 → y ∈ hairerTimeWindow) {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (hg : IsScaledTest g z R A) :
    |parabolicSemigroup.pairing (M.regPi z τ) g| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A * R ^ 5) *
        ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ), |τ i| * R ^ 𝒯.deg i := by
  have hlim := M.tendsto_integral_regPi_mul_of_scaled_onWindowAt_near hPi hCPi hGam hgrowth hdeg hball
    hτ hg
  have hlim' := M.tendsto_integral_regPi_mul_sum_onWindowAt hPi hCPi hGam hgrowth hdeg hball hτ hg
  rw [tendsto_nhds_unique hlim hlim']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [abs_mul]
  have := (M.tendsto_abs_pairing_regPi_single_of_scaled_onWindowAt_near hPi hCPi hGam hgrowth hdeg
    (Finset.mem_filter.1 hi).2 hball hg).2
  calc _ ≤ |τ i| * (r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A * R ^ 5) * R ^ 𝒯.deg i) := by
        gcongr
    _ = _ := by ring

end Model

end RegularityStructures

end
