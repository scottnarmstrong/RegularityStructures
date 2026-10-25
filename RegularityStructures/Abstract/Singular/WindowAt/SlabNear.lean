/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.WindowAt.PairingNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Model bound at slab base points, near-pair `Γ`-bounds

The model bound (2.15) for window models at base points `z` with `0 ≤ z₀ ≤ 1`:
`|⟨Π_z τ, g⟩| ≤ C K₀ (A R⁵) ∑_i |τ_i| R^{deg i}` for `g` scaled at `z`, for models whose `Γ`-bounds
hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ} {g : ParabolicSpace → ℝ}
  {z : ParabolicSpace} {R A : ℝ}

/-- **Window model bound (2.15) at slab base points**: `0 ≤ z.1 ≤ 1`. -/
theorem abs_pairing_regPi_le_of_scaled_slabAt_near (hPi : M.PiBoundOn γ CPi hairerTimeWindow)
    (hCPi : 0 ≤ CPi) (hGam : M.GammaNearOn γ CGam hairerTimeWindow)
    (hgrowth : M.HasQualitativeGrowthAt γ z) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hz0 : 0 ≤ z.1) (hz1 : z.1 ≤ 1) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    (hg : IsScaledTest g z R A) :
    |parabolicSemigroup.pairing (M.regPi z τ) g| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A * R ^ 5) *
        ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ), |τ i| * R ^ 𝒯.deg i :=
  M.abs_pairing_regPi_le_of_scaled_onWindowAt_near hPi hCPi hGam hgrowth hdeg
    (fun _ hy => ball_subset_hairerTimeWindow hz0 hz1 hy) hτ hg

end Model

end RegularityStructures

end
