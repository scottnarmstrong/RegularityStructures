/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Window.BasicNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# The standing hypotheses of the extension estimates, near-pair `Γ`-bounds

`ExtSettingWNear` assumes the bounds `PiBoundOn γ CPi` and `GammaNearOn γ CGam` only on Hairer's
window `hairerTimeWindow = [-1, 2] × ℝ³`, together with a qualitative growth model (used only for
the existence and linearity of the pairings and for identities, never in a constant) and the degree
condition `-4 < deg j` for all `deg j < γ`.

The structural lemmas about `τ = Γ_{yx} e_i` for base points in the window: `τ ∈ V ∩ T_{<γ}`
(`ExtSettingWNear.gammaMap_single_mem`), its support (`ExtSettingWNear.gammaMap_single_support`) and
`|τ_j| ≤ max(C_Γ, 1) d^{deg i − deg j}` (`ExtSettingWNear.abs_gammaMap_single_le`).

The `Γ`-bound `GammaNearOn` (`RegularityStructures.Abstract.ModelNear`) holds only for near pairs
and replaces `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

/-- The standing hypotheses of the extension theorem estimates, window version: the model bounds
hold on `hairerTimeWindow`, with a qualitative growth model. -/
structure ExtSettingWNear (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (N : ℕ) (γ : ℝ)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ))
    (CPi CGam : ℝ) : Prop where
  profile : ShellProfile h N
  realising : M.IsRealisingP h γ P I V
  integration : IsAbstractIntegration P V I 2
  sector : 𝒯.IsSector V
  basis_mem : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V
  deg_gtV : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j
  deg_gt4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j
  piBound : M.PiBoundOn γ CPi hairerTimeWindow
  gammaBound : M.GammaNearOn γ CGam hairerTimeWindow
  piBound_nonneg : 0 ≤ CPi
  growth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
    M.GrowthModel γ C' C'' ρP ρG p q
  poly_largeV : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
    ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N'
  integration_poly : ∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0
  poly_le : N' ≤ N

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ} {γ CPi CGam : ℝ}
  {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

/-- `τ = Γ_{yx} e_i` lies in `V ∩ T_{<γ}`. -/
theorem ExtSettingWNear.gammaMap_single_mem (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (x y : ParabolicSpace) :
    M.gammaMap y x (Pi.single i 1) ∈ V ∧
      M.gammaMap y x (Pi.single i 1) ∈ lowerSubspace 𝒯.deg γ :=
  ⟨S.sector.invariant _ (M.gamma y x).2 _ hVi,
    (M.isGradedUnipotent_gammaMap y x).map_lowerSubspace (single_mem_lowerSubspace hi 1)⟩

/-- A nonzero coordinate `τ_j` of `τ = Γ_{yx} e_i` has `e_j ∈ V`, `deg j ≤ deg i`. -/
theorem ExtSettingWNear.gammaMap_single_support (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (x y : ParabolicSpace) {j : ι}
    (hj : M.gammaMap y x (Pi.single i 1) j ≠ 0) :
    (Pi.single j 1 : ι → ℝ) ∈ V ∧ 𝒯.deg j < γ ∧ 𝒯.deg j ≤ 𝒯.deg i := by
  obtain ⟨hτV, hτl⟩ := S.gammaMap_single_mem hi hVi x y
  refine ⟨S.basis_mem _ hτV j hj, ?_, ?_⟩
  · by_contra hge
    exact hj (hτl j (not_lt.1 hge))
  · by_contra hge
    by_cases hji : j = i
    · exact hge (by rw [hji])
    · exact hj ((M.isGradedUnipotent_gammaMap y x).apply_single_of_le hji
        (not_le.1 hge).le)

/-- The coordinates of `τ = Γ_{yx} e_i` for `x, y` in the window:
`|τ_j| ≤ max(C_Γ, 1) d^{deg i − deg j}`. -/
theorem ExtSettingWNear.abs_gammaMap_single_le (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) {x y : ParabolicSpace}
    (hx : x ∈ hairerTimeWindow) (hy : y ∈ hairerTimeWindow)
    (hxy : parabolicNorm (y - x) ≤ gammaNearRadius) {j : ι}
    (hj : M.gammaMap y x (Pi.single i 1) j ≠ 0) :
    |M.gammaMap y x (Pi.single i 1) j| ≤
      max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i - 𝒯.deg j) := by
  obtain ⟨-, -, hji⟩ := S.gammaMap_single_support hi hVi x y hj
  by_cases hjeq : j = i
  · subst hjeq
    rw [(M.isGradedUnipotent_gammaMap y x).apply_single_self, abs_one, sub_self,
      Real.rpow_zero, mul_one]
    exact le_max_right _ _
  · have hlt : 𝒯.deg j < 𝒯.deg i := by
      refine lt_of_le_of_ne hji fun h' => hj ?_
      exact (M.isGradedUnipotent_gammaMap y x).apply_single_of_le hjeq h'.symm.le
    have hG := M.abs_gammaMap_single_le_of_window_near S.gammaBound hi hlt hx hy hxy
    exact hG.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (parabolicNorm_nonneg _) _))

end Model

end RegularityStructures

end
