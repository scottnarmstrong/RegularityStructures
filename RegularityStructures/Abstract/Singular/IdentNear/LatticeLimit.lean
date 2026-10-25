/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.LatticeAvg
public import RegularityStructures.Abstract.Singular.Ident.LatticeLimit

/-!
# Pointwise convergence of the lattice average, near-pair `Γ`-bounds

For every `y`, `latticeAvg 𝒯 g γ f n y → R̃f(y) = pointwiseReconstruct g f y` as `n → ∞`
(`tendsto_latticeAvg_wnear`). Outside the slab both sides vanish eventually; at a point `y` of the
slab, the cells containing `y` are centred at lattice points `z` of the slab with
`d(y, z) ≤ 8 · 2^{-n} ≤ min(w_z, w_y)` for large `n`, so the singular increment bound gives
`|latticeAvg n y − R̃f(y)| ≲ ∑_j (8 · 2^{-n})^{γ − deg j} → 0`.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

theorem latticeAvg_eq_zero_of_not_mem_wnear (n : ℕ) (y : ParabolicSpace)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    (h : ∀ k, latticeCell n k y ≠ 0 → latticePoint n k ∉ timeSlab T) :
    latticeAvg 𝒯 g γ f n y = 0 := by
  have := abs_finsum_cell_le (n := n) (y := y) (B := 0)
    (a := fun k => fnComb 𝒯 g γ (latticePoint n k) (f (latticePoint n k)) y) fun k hk => by
      rw [S.hf0 _ (h k hk), fnComb_zero_right, abs_zero]
  exact abs_nonpos_iff.1 this

theorem pointwiseReconstruct_eq_zero_of_not_mem_wnear (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {y : ParabolicSpace} (hy : y ∉ timeSlab T) : pointwiseReconstruct g f y = 0 := by
  simp [pointwiseReconstruct, S.hf0 y hy]

/-- Convergence at a point of the slab. -/
theorem tendsto_latticeAvg_of_mem_timeSlab_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {y : ParabolicSpace} (hy : y ∈ timeSlab T) :
    Tendsto (fun n => latticeAvg 𝒯 g γ f n y) atTop (𝓝 (pointwiseReconstruct g f y)) := by
  set F : Finset ι := Finset.univ.filter (fun j => 𝒯.deg j < γ) with hF
  set r : ℝ := Real.sqrt y.1 with hr
  have hy0 : 0 < y.1 := hy.1
  have hr0 : 0 < r := Real.sqrt_pos.2 hy0
  have hr2 : r ^ 2 = y.1 := Real.sq_sqrt hy0.le
  have hr1 : r ≤ 1 := by
    calc r ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (hy.2.trans S.hT)
      _ = 1 := Real.sqrt_one
  have hwy : singularWeight timeZeroDist y = r := singularWeight_timeZeroDist_eq hy S.hT
  set Wc : ℝ := max 1 ((r / 2) ^ (η - γ)) with hWc
  set B : ℕ → ℝ := fun n => ∑ j ∈ F, Cf * Wc * |g y j y| * (8 * ((2 : ℝ) ^ n)⁻¹) ^ (γ - 𝒯.deg j)
    with hB
  have hs8 : Tendsto (fun n : ℕ => 8 * ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_two_pow.const_mul (8 : ℝ)
  have hBlim : Tendsto B atTop (𝓝 0) := by
    have h := tendsto_finsetSum F fun j hj => (show Tendsto (fun n : ℕ =>
        Cf * Wc * |g y j y| * (8 * ((2 : ℝ) ^ n)⁻¹) ^ (γ - 𝒯.deg j)) atTop
        (𝓝 (Cf * Wc * |g y j y| * 0)) from by
      have hp : 0 < γ - 𝒯.deg j := by linarith [(Finset.mem_filter.1 hj).2]
      have h1 := ((Real.continuous_rpow_const hp.le).tendsto 0).comp hs8
      rw [Real.zero_rpow hp.ne'] at h1
      exact h1.const_mul _)
    simpa using h
  have hev : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ n)⁻¹ < r / 16 :=
    eventually_inv_two_pow_lt (by positivity)
  have hbound : ∀ᶠ n : ℕ in atTop,
      |latticeAvg 𝒯 g γ f n y - pointwiseReconstruct g f y| ≤ B n := by
    filter_upwards [hev] with n hn
    refine abs_finsum_cell_sub_le fun k hk => ?_
    obtain ⟨h1, h2, h3⟩ := latticeCell_geometry hk
    set z := latticePoint n k with hz
    set s : ℝ := ((2 : ℝ) ^ n)⁻¹ with hs
    have hs0 : 0 < s := by positivity
    have hs2 : s ^ 2 < y.1 / 256 := by
      have : s < r / 16 := hn
      nlinarith
    have hz1 : y.1 / 4 < z.1 := by linarith
    have hzslab : z ∈ timeSlab T := ⟨by linarith, by linarith [hy.2]⟩
    have hwz : singularWeight timeZeroDist z = Real.sqrt z.1 :=
      singularWeight_timeZeroDist_eq hzslab S.hT
    have hrz : r / 2 ≤ Real.sqrt z.1 := by
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have hd : parabolicNorm (y - z) ≤ min (singularWeight timeZeroDist z)
        (singularWeight timeZeroDist y) := by
      rw [hwz, hwy]
      refine le_min ?_ ?_ <;> linarith
    refine (abs_fnComb_sub_pointwiseReconstruct_le_of_close_wnear hg S hzslab hy hd).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    have hjγ := (Finset.mem_filter.1 hj).2
    have hp : 0 ≤ γ - 𝒯.deg j := by linarith
    have hdn : parabolicNorm (y - z) ^ (γ - 𝒯.deg j) ≤ (8 * s) ^ (γ - 𝒯.deg j) :=
      Real.rpow_le_rpow (parabolicNorm_nonneg _) h3 hp
    have hmin : min (singularWeight timeZeroDist z) (singularWeight timeZeroDist y) ^ (η - γ) ≤
        Wc := by
      set m := min (singularWeight timeZeroDist z) (singularWeight timeZeroDist y) with hm
      have hm1 : m ≤ 1 := (min_le_left _ _).trans (singularWeight_le_one _ _)
      have hm2 : r / 2 ≤ m := by rw [hm, hwz, hwy]; exact le_min hrz (by linarith)
      by_cases he : 0 ≤ η - γ
      · exact (Real.rpow_le_one (by linarith) hm1 he).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_nonpos (by linarith) hm2 (not_le.1 he).le).trans
          (le_max_right _ _)
    have hg0 := abs_nonneg (g y j y)
    have hW0 : 0 ≤ Wc := (zero_le_one).trans (le_max_left _ _)
    calc Cf * parabolicNorm (y - z) ^ (γ - 𝒯.deg j) *
          min (singularWeight timeZeroDist z) (singularWeight timeZeroDist y) ^ (η - γ) *
            |g y j y|
        ≤ Cf * (8 * s) ^ (γ - 𝒯.deg j) * Wc * |g y j y| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul
            (mul_le_mul_of_nonneg_left hdn S.hCf) hmin (Real.rpow_nonneg (le_min
              (singularWeight_pos (timeZeroDist_pos_of_mem_timeSlab hzslab)).le
              (singularWeight_pos (timeZeroDist_pos_of_mem_timeSlab hy)).le) _)
            (mul_nonneg S.hCf (Real.rpow_nonneg (by positivity) _))) hg0
      _ = Cf * Wc * |g y j y| * (8 * s) ^ (γ - 𝒯.deg j) := by ring
  have hlim : Tendsto (fun n => latticeAvg 𝒯 g γ f n y - pointwiseReconstruct g f y) atTop
      (𝓝 0) :=
    squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hbound) hBlim
  exact tendsto_sub_nhds_zero_iff.1 hlim

/-- **Pointwise convergence of the lattice average** to the pointwise reconstruction. -/
theorem tendsto_latticeAvg_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (y : ParabolicSpace) :
    Tendsto (fun n => latticeAvg 𝒯 g γ f n y) atTop (𝓝 (pointwiseReconstruct g f y)) := by
  by_cases hy : y ∈ timeSlab T
  · exact tendsto_latticeAvg_of_mem_timeSlab_wnear hg S hy
  · rw [pointwiseReconstruct_eq_zero_of_not_mem_wnear S hy]
    by_cases hy0 : y.1 ≤ 0
    · refine tendsto_const_nhds.congr fun n => ?_
      symm
      refine latticeAvg_eq_zero_of_not_mem_wnear n y S fun k hk hz => ?_
      obtain ⟨h1, -, -⟩ := latticeCell_geometry hk
      linarith [hz.1]
    · have hT : T < y.1 := by
        by_contra hle
        exact hy ⟨not_le.1 hy0, not_lt.1 hle⟩
      have hev : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ n)⁻¹ < min 1 ((y.1 - T) / 2) :=
        eventually_inv_two_pow_lt (lt_min one_pos (by linarith))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      symm
      refine latticeAvg_eq_zero_of_not_mem_wnear n y S fun k hk hz => ?_
      obtain ⟨-, h2, -⟩ := latticeCell_geometry hk
      have hs0 : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
      have h1 : ((2 : ℝ) ^ n)⁻¹ < 1 := hn.trans_le (min_le_left _ _)
      have h3 : ((2 : ℝ) ^ n)⁻¹ < (y.1 - T) / 2 := hn.trans_le (min_le_right _ _)
      nlinarith [hz.2]

end Model

end RegularityStructures
