/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesAux
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Elementary facts for the series bound of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`, near-pair `Γ`-bounds

The coordinates of `τ = f(y) − Γ_{yx} f(x)` satisfy `|τ_i| ≤ C_f d^{γ−deg i} W^{η−γ}`
(`abs_tau_le_win_near`), `τ ∈ T_{<γ}` (`tau_mem_lowerSubspace_win_near`), and a nonzero coordinate
of `τ` belongs to a basis vector of `V` of degree `< γ` (`tau_support_slab_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {x y : ParabolicSpace}

/-- The coordinates of `τ = f(y) − Γ_{yx} f(x)` below `γ`:
`|τ_i| ≤ C_f d^{γ − deg i} W^{η − γ}` (window setting). -/
theorem abs_tau_le_win_near (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    (P : SlabPair T x y) {i : ι} (hi : 𝒯.deg i < γ) :
    |(f y - M.gammaMap y x (f x)) i| ≤ Cf * parabolicNorm (y - x) ^ (γ - 𝒯.deg i) *
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (η - γ) :=
  S.hf.2 x P.hx y P.hy (timeZeroDist_pos_of_mem_timeSlab P.hx)
    (timeZeroDist_pos_of_mem_timeSlab P.hy) P.d_le_W i hi

/-- `τ = f(y) − Γ_{yx} f(x) ∈ T_{<γ}` (window setting). -/
theorem tau_mem_lowerSubspace_win_near (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    (x y : ParabolicSpace) : f y - M.gammaMap y x (f x) ∈ lowerSubspace 𝒯.deg γ :=
  Submodule.sub_mem _ (S.hfT y) ((M.isGradedUnipotent_gammaMap y x).map_lowerSubspace (S.hfT x))

/-- A nonzero coordinate of `τ` belongs to a basis vector of `V` of degree `< γ`
(window setting). -/
theorem tau_support_slab_win_near {V : Submodule ℝ (ι → ℝ)}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hfV : ∀ z, f z ∈ V) (x y : ParabolicSpace) {i : ι}
    (h : (f y - M.gammaMap y x (f x)) i ≠ 0) :
    (Pi.single i 1 : ι → ℝ) ∈ V ∧ 𝒯.deg i < γ := by
  refine ⟨hVb _ (Submodule.sub_mem _ (hfV y) (hV.invariant _ (M.gamma y x).2 _ (hfV x))) i h, ?_⟩
  by_contra hge
  exact h (M.tau_mem_lowerSubspace_win_near S x y i (not_lt.1 hge))

end Model

end RegularityStructures

end
