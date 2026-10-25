/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Ident.Pointwise
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Ident.FunctionModel
public import RegularityStructures.Abstract.ProductBoundsNear

/-!
# Pointwise comparison of `Π_z f(z)` with `R̃f`, near-pair `Γ`-bounds

Control of `G_z(y) − R̃f(y)` by the modelled increments `f(y) − Γ_{yz} f(z)`, the increment bound
for `d(y, z) ≤ min(w_z, w_y)`, and a crude uniform bound on `G_z(y)`, in the window layer setting
`LayerSettingWNear`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.

Near pairs are those at distance at most `gammaNearRadius = 4`; the crude bound
`abs_fnComb_le_of_slab_wnear` therefore additionally assumes `d(y, z) ≤ 4`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

private theorem term_bound {Cf CG w d m a e0 : ℝ} (hCf : 0 ≤ Cf) (hCG : 0 ≤ CG) (hw0 : 0 < w)
    (hw1 : w ≤ 1) (hd0 : 0 ≤ d) (hd : d ≤ 8 * w) (ha : 0 ≤ a) (hma : e0 ≤ m + a) :
    Cf * w ^ m * ((1 + CG) * d ^ a) ≤ Cf * (1 + CG) * 8 ^ a * w ^ e0 := by
  have h1 : d ^ a ≤ (8 * w) ^ a := Real.rpow_le_rpow hd0 hd ha
  rw [Real.mul_rpow (by norm_num) hw0.le] at h1
  have h2 : w ^ m * w ^ a = w ^ (m + a) := (Real.rpow_add hw0 m a).symm
  have h3 : w ^ (m + a) ≤ w ^ e0 := Real.rpow_le_rpow_of_exponent_ge hw0 hw1 hma
  have h8 : (0 : ℝ) ≤ 8 ^ a := Real.rpow_nonneg (by norm_num) _
  have hwm : 0 ≤ w ^ m := Real.rpow_nonneg hw0.le _
  calc Cf * w ^ m * ((1 + CG) * d ^ a) = Cf * (1 + CG) * (w ^ m * d ^ a) := by ring
    _ ≤ Cf * (1 + CG) * (w ^ m * (8 ^ a * w ^ a)) := by
        gcongr
    _ = Cf * (1 + CG) * 8 ^ a * (w ^ m * w ^ a) := by ring
    _ ≤ Cf * (1 + CG) * 8 ^ a * w ^ e0 := by
        rw [h2]; gcongr

private theorem exponent_ineq {η dj di : ℝ} (hj : dj ≤ 0) (hji : dj ≤ di) :
    min η 0 ≤ min (η - di) 0 + (di - dj) := by
  by_cases h : η - di ≤ 0
  · rw [min_eq_left h]; linarith [min_le_left η 0]
  · rw [min_eq_right (le_of_not_ge h)]; linarith [min_le_right η 0]


namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

/-- `G_z(y) − R̃f(y)` is controlled by the modelled increments `f(y) − Γ_{yz} f(z)`. -/
theorem abs_fnComb_sub_pointwiseReconstruct_le_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (z y : ParabolicSpace) :
    |fnComb 𝒯 g γ z (f z) y - pointwiseReconstruct g f y| ≤
      ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ),
        |(f y - M.gammaMap y z (f z)) j| * |g y j y| := by
  rw [fnComb_eq_fnComb_gammaMap hg (S.hfT z) y, pointwiseReconstruct_eq_fnComb y (S.hfT y)]
  unfold fnComb
  rw [← Finset.sum_sub_distrib, ← abs_neg, ← Finset.sum_neg_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← abs_mul]
  refine le_of_eq (congrArg _ ?_)
  simp only [Pi.sub_apply]
  ring

/-- The increment bound: for `z, y` in the slab with `d(y, z) ≤ min(w_z, w_y)`. -/
theorem abs_fnComb_sub_pointwiseReconstruct_le_of_close_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {z y : ParabolicSpace} (hz : z ∈ timeSlab T)
    (hy : y ∈ timeSlab T)
    (hd : parabolicNorm (y - z) ≤
      min (singularWeight timeZeroDist z) (singularWeight timeZeroDist y)) :
    |fnComb 𝒯 g γ z (f z) y - pointwiseReconstruct g f y| ≤
      ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ),
        Cf * parabolicNorm (y - z) ^ (γ - 𝒯.deg j) *
          min (singularWeight timeZeroDist z) (singularWeight timeZeroDist y) ^ (η - γ) *
          |g y j y| := by
  refine (abs_fnComb_sub_pointwiseReconstruct_le_wnear hg S z y).trans
    (Finset.sum_le_sum fun j hj => ?_)
  exact mul_le_mul_of_nonneg_right
    (S.hf.2 z hz y hy (timeZeroDist_pos_of_mem_timeSlab hz) (timeZeroDist_pos_of_mem_timeSlab hy)
      hd j (Finset.mem_filter.1 hj).2) (abs_nonneg _)

/-- The entries of `Γ_{yz} f(z)` in degrees `≤ 0` are bounded by `w_z^{min(η, 0)}` when
`d(y, z) ≤ 8 w_z`. -/
theorem abs_gammaMap_apply_le_of_slab_wnear (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {z y : ParabolicSpace} (hz : z ∈ timeSlab T) (hy : y ∈ hairerTimeWindow)
    (hd : parabolicNorm (y - z) ≤ 8 * singularWeight timeZeroDist z)
    (hd4 : parabolicNorm (y - z) ≤ 4) {j : ι}
    (hj : 𝒯.deg j ≤ 0) :
    |M.gammaMap y z (f z) j| ≤
      Cf * (1 + max CGam 0) * identDomConst 𝒯 * singularWeight timeZeroDist z ^ min η 0 := by
  set w := singularWeight timeZeroDist z with hw
  have hρ := timeZeroDist_pos_of_mem_timeSlab hz
  have hw0 : 0 < w := singularWeight_pos hρ
  have hw1 : w ≤ 1 := singularWeight_le_one _ _
  have hCG : 0 ≤ max CGam 0 := le_max_right _ _
  have hG' : M.GammaNearOn γ (max CGam 0) hairerTimeWindow :=
    fun i j hi hji x hx y hy hxy => (S.hGam i j hi hji x hx y hy hxy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
  have hzW := RegularityStructures.mem_hairerTimeWindow_of_mem_timeSlab S.hT hz
  have hdec : M.gammaMap y z (f z) j = ∑ i, f z i * M.gammaMap y z (Pi.single i 1) j := by
    conv_lhs => rw [eq_sum_single (f z)]
    simp [map_sum, Finset.sum_apply]
  have hA : 0 ≤ Cf * (1 + max CGam 0) := mul_nonneg S.hCf (by linarith)
  have hterm : ∀ i, |f z i * M.gammaMap y z (Pi.single i 1) j| ≤
      Cf * (1 + max CGam 0) * (8 : ℝ) ^ (𝒯.deg i - 𝒯.deg j) * w ^ min η 0 := by
    intro i
    have hpos : 0 ≤ Cf * (1 + max CGam 0) * (8 : ℝ) ^ (𝒯.deg i - 𝒯.deg j) * w ^ min η 0 :=
      mul_nonneg (mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hw0.le _)
    by_cases hfi : f z i = 0
    · rw [hfi, zero_mul, abs_zero]; exact hpos
    · have hi : 𝒯.deg i < γ := by
        by_contra hge
        exact hfi ((mem_lowerSubspace).1 (S.hfT z) i (not_lt.1 hge))
      by_cases hji : 𝒯.deg i < 𝒯.deg j
      · rw [M.gammaMap_single_apply_eq_zero z y hji, mul_zero, abs_zero]; exact hpos
      · have hji' : 𝒯.deg j ≤ 𝒯.deg i := not_lt.1 hji
        rw [abs_mul]
        have h1 := S.hf.1 z hz hρ i hi
        have h2 := M.abs_gammaMap_single_apply_le_near hG' hCG hzW hy
          (hd4.trans (by unfold gammaNearRadius; exact le_rfl)) hi hji'
        have h3 : |f z i| * |M.gammaMap y z (Pi.single i 1) j| ≤
            Cf * w ^ min (η - 𝒯.deg i) 0 *
              ((1 + max CGam 0) * parabolicNorm (y - z) ^ (𝒯.deg i - 𝒯.deg j)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg S.hCf (Real.rpow_nonneg hw0.le _))
        refine h3.trans ?_
        exact term_bound S.hCf hCG hw0 hw1 (parabolicNorm_nonneg _) hd (by linarith)
          (exponent_ineq hj hji')
  rw [hdec]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  have hw' : 0 ≤ w ^ min η 0 := Real.rpow_nonneg hw0.le _
  have hsum : ∑ i, Cf * (1 + max CGam 0) * (8 : ℝ) ^ (𝒯.deg i - 𝒯.deg j) * w ^ min η 0 =
      Cf * (1 + max CGam 0) * (∑ i, (8 : ℝ) ^ (𝒯.deg i - 𝒯.deg j)) * w ^ min η 0 := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hsum]
  gcongr
  exact sum_rpow_eight_le_identDomConst 𝒯 j

/-- **Crude uniform bound**: for `z` in the slab, `y` in the window with `d(y, z) ≤ 8 w_z`,
`|G_z(y)| ≤ (∑_{deg j < γ} |g_{y,j}(y)|) · Cf (1 + C_Γ⁺) K · w_z^{min(η, 0)}`. -/
theorem abs_fnComb_le_of_slab_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {z y : ParabolicSpace} (hz : z ∈ timeSlab T)
    (hy : y ∈ hairerTimeWindow) (hd : parabolicNorm (y - z) ≤ 8 * singularWeight timeZeroDist z)
    (hd4 : parabolicNorm (y - z) ≤ 4) :
    |fnComb 𝒯 g γ z (f z) y| ≤
      (∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), |g y j y|) *
        (Cf * (1 + max CGam 0) * identDomConst 𝒯 * singularWeight timeZeroDist z ^ min η 0) := by
  rw [fnComb_eq_fnComb_gammaMap hg (S.hfT z) y]
  unfold fnComb
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [abs_mul, mul_comm]
  have hjγ := (Finset.mem_filter.1 hj).2
  by_cases hj0 : 𝒯.deg j ≤ 0
  · exact mul_le_mul_of_nonneg_left (abs_gammaMap_apply_le_of_slab_wnear S hz hy hd hd4 hj0) (abs_nonneg _)
  · rw [diag_eq_zero_of_isSmooth hg S.hPi (not_le.1 hj0) hjγ hy, abs_zero, zero_mul, zero_mul]

end Model

end RegularityStructures
