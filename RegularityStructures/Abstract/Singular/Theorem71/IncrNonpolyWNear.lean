/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.FarNonpolyWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Theorem71.RemVecGApi

/-!
# Non-polynomial increments of `𝒦_γ f + R_γ f` for a kernel pair, near-pair `Γ`-bounds

For `x, y` in the slab with `d(y, x) ≤ ‖x, y‖_P` and `j` not a polynomial index,
`|(F(y) − Γ_{yx} F(x))_j| ≤ |ι| C_I C_f d^{γ+2−deg j} ‖x, y‖_P^{α∧η−γ}`, `F = 𝒦_γ f + R_γ f`
(`abs_kGammaRemG_sub_gamma_apply_le_of_notMem_range_win_near`). Only the singular bound of `f` and
the qualitative growth model are used.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

/-- Increments of the non-polynomial components of `𝒦_γ f + R_γ f`, window models. -/
theorem abs_kGammaRemG_sub_gamma_apply_le_of_notMem_range_win_near
    {γ η α Cf CPi CGam T CI : ℝ}
    {M : Model 𝒯 parabolicSemigroup} {h r : ParabolicSpace → ℝ} {N : ℕ}
    {f : ParabolicSpace → ι → ℝ} (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    (hh : ShellProfile h N)
    {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}
    (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ,
      (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N')
    (hCI : ∀ i j, |I (Pi.single i 1) j| ≤ CI) (hfV : ∀ z, f z ∈ V)
    {x y : ParabolicSpace} (hx : x ∈ timeSlab T) (hy : y ∈ timeSlab T)
    (hd : parabolicSemigroup.scaleDist y x ≤
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y))
    {j : ι} (hj : j ∉ Set.range P.emb) :
    |(M.kGammaRemG h r P I γ f y - M.gammaMap y x (M.kGammaRemG h r P I γ f x)) j| ≤
      Fintype.card ι * CI * (Cf * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j) *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
          (min α η - γ)) := by
  have hsplit : M.kGammaRemG h r P I γ f y - M.gammaMap y x (M.kGammaRemG h r P I γ f x) =
      (M.kGammaS h P I γ f y - M.gammaMap y x (M.kGammaS h P I γ f x)) +
      (M.remVecG r P γ f y - M.gammaMap y x (M.remVecG r P γ f x)) := by
    unfold kGammaRemG
    rw [map_add]; abel
  rw [hsplit, Pi.add_apply, remVecG_sub_gammaMap_apply_of_notMem_range M r P γ f x y hj,
    add_zero]
  exact abs_kGammaS_sub_gamma_nonpoly_le_singular_win_near S hh hreal hI hV hVb hdeg hN' hCI hfV hx
    hy hd hj

end Model

end RegularityStructures

end
