/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.FarNonpolyW
public import RegularityStructures.Abstract.Singular.KGamma.SupMainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Theorem512.Sup
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.Singular.KGamma.FarNonpolyW`

The statements of `RegularityStructures.Abstract.Singular.KGamma.FarNonpolyW` that involve
`Γ`-bounds, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

/-- **Singular Schauder, non-polynomial components** [Hai14, Prop. 6.16]: for `x, y` in the slab
with `d(y, x) ≤ ‖x, y‖_P` and `j ∉ T̄`,
`|(𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x))_j| ≤ |ι| C_I C_f d^{γ + 2 − deg j} ‖x, y‖_P^{α ∧ η − γ}`. -/
theorem abs_kGammaS_sub_gamma_nonpoly_le_singular_win_near {γ η α Cf CPi CGam T CI : ℝ}
    {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {h : ParabolicSpace → ℝ} {N : ℕ}
    {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ,
      (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N')
    (hCI : ∀ i j, |I (Pi.single i 1) j| ≤ CI) (hfV : ∀ z, f z ∈ V)
    {x y : ParabolicSpace} (hx : x ∈ timeSlab T) (hy : y ∈ timeSlab T)
    (hd : parabolicSemigroup.scaleDist y x ≤
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y))
    {j : ι} (hj : j ∉ Set.range P.emb) :
    |(kGammaS M h P I γ f y - M.gammaMap y x (kGammaS M h P I γ f x)) j| ≤
      Fintype.card ι * CI * (Cf * parabolicSemigroup.scaleDist y x ^ (γ + 2 - 𝒯.deg j) *
        min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ)) := by
  rw [kGammaS_sub_gamma_apply_of_notMem_range_win hh hreal hI hV hVb hdeg S.hgrowth hN'
    S.hfT hfV hj x y, linearMap_apply_eq_sum]
  set τ := f y - M.gammaMap y x (f x) with hτ
  have hτV : τ ∈ V :=
    Submodule.sub_mem _ (hfV y) (hV.invariant _ (M.gamma y x).2 _ (hfV x))
  have hτl : τ ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ (S.hfT y) ((M.isGradedUnipotent_gammaMap y x).map_lowerSubspace
      (S.hfT x))
  set W := min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with hW
  set d := parabolicSemigroup.scaleDist y x with hdd
  have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg _ _
  have hWpos : 0 < W := lt_min (KGammaSup.weight_pos hx) (KGammaSup.weight_pos hy)
  have hW1 : W ≤ 1 := (min_le_left _ _).trans (singularWeight_le_one _ _)
  have hCf := S.hCf
  have hterm : ∀ i, |τ i * I (Pi.single i 1) j| ≤
      CI * (Cf * d ^ (γ + 2 - 𝒯.deg j) * W ^ (min α η - γ)) := by
    intro i
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI i j)
    have hnn : 0 ≤ Cf * d ^ (γ + 2 - 𝒯.deg j) * W ^ (min α η - γ) :=
      mul_nonneg (mul_nonneg hCf (Real.rpow_nonneg hd0 _)) (Real.rpow_nonneg hWpos.le _)
    by_cases hτi : τ i = 0
    · rw [hτi, zero_mul, abs_zero]; exact mul_nonneg hCI0 hnn
    · have hi : 𝒯.deg i < γ := by
        by_contra hge; exact hτi (hτl i (not_lt.1 hge))
      have hIi : I (Pi.single i 1) ∈ homogeneousSubspace 𝒯.deg (𝒯.deg i + 2) :=
        hI.map_homogeneous _ _ (hVb τ hτV i hτi) (single_mem_homogeneousSubspace i 1)
      by_cases hdj : 𝒯.deg j = 𝒯.deg i + 2
      · have hτb := S.hf.2 x hx y hy (timeZeroDist_pos_of_mem_timeSlab hx)
          (timeZeroDist_pos_of_mem_timeSlab hy) hd i hi
        have hexp : γ + 2 - 𝒯.deg j = γ - 𝒯.deg i := by rw [hdj]; ring
        have hWe : W ^ (η - γ) ≤ W ^ (min α η - γ) :=
          Real.rpow_le_rpow_of_exponent_ge hWpos hW1 (by linarith [min_le_right α η])
        have hτb' : |τ i| ≤ Cf * d ^ (γ + 2 - 𝒯.deg j) * W ^ (min α η - γ) := by
          rw [hexp]
          refine hτb.trans ?_
          exact mul_le_mul_of_nonneg_left hWe (mul_nonneg hCf (Real.rpow_nonneg hd0 _))
        rw [abs_mul, mul_comm]
        exact mul_le_mul (hCI i j) hτb' (abs_nonneg _) hCI0
      · rw [hIi j hdj, mul_zero, abs_zero]; exact mul_nonneg hCI0 hnn
  calc |∑ i, τ i * I (Pi.single i 1) j|
      ≤ ∑ _i : ι, CI * (Cf * d ^ (γ + 2 - 𝒯.deg j) * W ^ (min α η - γ)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Model

end RegularityStructures

end
