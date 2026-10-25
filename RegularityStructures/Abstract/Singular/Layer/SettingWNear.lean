/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.WindowAt.SlabNear
public import RegularityStructures.Abstract.WeightedSingularCubeNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The window setting of the layer bound, near-pair `Γ`-bounds

`LayerSettingWNear` bundles the hypotheses of the layer bound [Hai14, Proposition 6.9] (lattice
form) in window form: the model bounds `PiBoundOn γ CPi` and `GammaNearOn γ CGam` on Hairer's window
`hairerTimeWindow = [-1, 2] × ℝ³`, the singular bound on `f` on the slab `(0, T]`, and `T ≤ 1`.
Every base point at which a quantitative model bound is evaluated lies in the slab, so the unit
parabolic ball about it lies in the window, and all constants depend only on the window constants
`CPi`, `CGam`.

The field `hgrowth` is qualitative: some `Model.GrowthModel` (with arbitrary constants, weights and
exponents) exists. It is used only for identities, convergence and measurability, never in a
constant (`LayerSettingWNear.hasQualitativeGrowthAt`). `LayerSettingWNear.abs_pairing_le` is the
window pairing bound at slab base points.

The `Γ`-bound `GammaNearOn` (`RegularityStructures.Abstract.ModelNear`) holds only for near pairs
and replaces `GammaBoundOn`.
-/

@[expose] public section

namespace RegularityStructures

/-- Window hypotheses of the layer bound (Hairer, arXiv:1303.5113v4, Prop. 6.9, lattice form):
model bounds on `hairerTimeWindow`, qualitative existence of a growth model, and `T ≤ 1`. -/
structure LayerSettingWNear {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
    (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
    (γ η α Cf CPi CGam T : ℝ) : Prop where
  hγ : 0 < γ
  hPi : M.PiBoundOn γ CPi hairerTimeWindow
  hCPi : 0 ≤ CPi
  hGam : M.GammaNearOn γ CGam hairerTimeWindow
  hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
    M.GrowthModel γ C' C'' ρP ρG p q
  hT : T ≤ 1
  hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j
  hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ
  hf : M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f
  hf0 : ∀ z, z ∉ timeSlab T → f z = 0
  hα : ∀ z i, f z i ≠ 0 → α ≤ 𝒯.deg i
  hαγ : α ≤ γ
  hαη : -2 < min α η
  hCf : 0 ≤ Cf

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}
  {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ}

namespace LayerSettingWNear

/-- The effective constant `max 1 CGam * CPi` is nonnegative. -/
theorem hK0 (S : LayerSettingWNear M f γ η α Cf CPi CGam T) : 0 ≤ max 1 CGam * CPi :=
  mul_nonneg (zero_le_one.trans (le_max_left _ _)) S.hCPi

theorem mem_timeSlab_of_ne_zero (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {z : ParabolicSpace} {i : ι} (h : f z i ≠ 0) : z ∈ timeSlab T := by
  by_contra hz
  exact h (by rw [S.hf0 z hz]; rfl)

theorem fst_le_one_of_mem_timeSlab (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {z : ParabolicSpace} (hz : z ∈ timeSlab T) : z.1 ≤ 1 :=
  hz.2.trans S.hT

/-- Pointwise qualitative growth at every base point, from the qualitative growth model. -/
theorem hasQualitativeGrowthAt (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    (x : ParabolicSpace) : M.HasQualitativeGrowthAt γ x := by
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  exact G.hasQualitativeGrowthAt x

/-- Window form of the pairing bound at a point of the time slab; the constant carries no
growth data. -/
theorem abs_pairing_le (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (hg : IsScaledTest g z R A)
    (hz : z ∈ timeSlab T) :
    |parabolicSemigroup.pairing (M.regPi z τ) g| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A * R ^ 5) *
        ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ), |τ i| * R ^ 𝒯.deg i :=
  M.abs_pairing_regPi_le_of_scaled_slabAt_near S.hPi S.hCPi S.hGam (S.hasQualitativeGrowthAt z)
    S.hdeg hz.1.le (S.fst_le_one_of_mem_timeSlab hz) hτ hg

variable {f₁ f₂ : ParabolicSpace → ι → ℝ} {C₁ C₂ : ℝ}

end LayerSettingWNear

end RegularityStructures

end
