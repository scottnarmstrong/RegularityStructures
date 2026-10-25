/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.MeasReconWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.KGamma.SeriesLargeG
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The large-scale form of the series for `𝒦_γ` on the time slab, near-pair `Γ`-bounds

For `x`, `y` in the time slab,
`polyUS n = ⟨Rf − Π_x f(x), K^{k,γ}_{n;yx}⟩ − ∑_{i : |k| ≥ deg i + 2} τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩`
[Hai14, (5.48)] (`polyUS_eq_large_of_slab_win_near`). Only the two centres `x` and `y` are used, and
the convergence of the lattice approximations of the shell derivatives at these centres follows from
the layer setting.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set Filter MeasureTheory

open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ}
  {γ CPi CGam : ℝ}

/-- **Large-scale form of the series on the slab** ([Hai14, (5.48)], singular case): for `x`, `y`
in the time slab of a layer setting,
`polyUS n = ⟨Rf − Π_x f(x), K^{k,γ}_{n;yx}⟩ − ∑_{i : |k| ≥ deg i + 2} τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩`. -/
theorem polyUS_eq_large_of_slab_win_near {f : ParabolicSpace → ι → ℝ} {γ' η α Cf T : ℝ}
    (hh : ShellProfile h N) (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S : LayerSettingWNear M f γ' η α Cf CPi CGam T) {x y : ParabolicSpace}
    (hx : x ∈ timeSlab T) (hy : y ∈ timeSlab T) (k : Fin 4 →₀ ℕ) (n : ℕ) :
    polyUS M h γ' f x y k n =
      (M.latticeRecon f (dTaylorKernel h k n (γ' + 2 - multiDeg k) x y) -
        parabolicSemigroup.pairing (M.regPi x (f x))
          (dTaylorKernel h k n (γ' + 2 - multiDeg k) x y)) -
      ∑ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2),
        (f y - M.gammaMap y x (f x)) i *
          parabolicSemigroup.pairing (fun t z => M.regPi y (Pi.single i 1) t z)
            (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w)) := by
  classical
  have hf := S.hfT
  obtain ⟨_, _, _, _, _, _, Gm⟩ := S.hgrowth
  have hdeg := S.hdeg
  have hcy := fun k n => M.tendsto_latticeApprox_lineIter_scaledShell_win_near hh hc S k n hy.2
  have hcx := fun k n => M.tendsto_latticeApprox_lineIter_scaledShell_win_near hh hc S k n hx.2
  set τ := f y - M.gammaMap y x (f x) with hτ
  have hΓ : M.gammaMap y x (f x) ∈ lowerSubspace 𝒯.deg γ' :=
    (M.isGradedUnipotent_gammaMap y x).map_lowerSubspace (hf x)
  have hτl : τ ∈ lowerSubspace 𝒯.deg γ' := Submodule.sub_mem _ (hf y) hΓ
  obtain ⟨C, -, hC⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  set φ : ParabolicSpace → ℝ := fun w => lineIter (multiDirs k) (scaledShell h n) (y - w) with hφ
  have hA : IsScaledTest φ y (((2 : ℝ) ^ n)⁻¹) _ := hC n y
  have hreg : M.regPi y (M.gammaMap y x (f x)) = M.regPi x (f x) := by
    funext t w; exact M.regPi_gammaMap y x (f x) t w
  have hpy : parabolicSemigroup.pairing (M.regPi y (f y)) φ =
      parabolicSemigroup.pairing (M.regPi y τ) φ +
        parabolicSemigroup.pairing (M.regPi x (f x)) φ := by
    have := M.pairing_regPi_sub_of_scaled_growth Gm hdeg (hf y) hΓ hA
    rw [hreg] at this
    rw [hτ, this]; ring
  have hsum := M.pairing_regPi_eq_sum_single_of_scaled_growth Gm hdeg hτl hA
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι)
    (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2)
    (fun i => τ i * parabolicSemigroup.pairing (M.regPi y (Pi.single i 1)) φ)
  rw [M.latticeRecon_dTaylorKernel_of_conv_growth hh hf Gm hdeg x y hcy hcx,
    M.pairing_regPi_dTaylorKernel_growth hh Gm hdeg (hf x)]
  unfold polyUS singShellPairing
  simp only [mul_sub, Finset.sum_sub_distrib]
  change _ + (M.latticeRecon f φ - parabolicSemigroup.pairing (M.regPi y (f y)) φ) - _ = _
  rw [hpy, hsum, ← hsplit]
  ring

end Model

end RegularityStructures

end
