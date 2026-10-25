/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.Pointwise
public import RegularityStructures.Abstract.Singular.Ident.LatticeAvg

/-!
# The lattice average of the model functions and its domination, near-pair `Γ`-bounds

`latticeAvg n y = ∑_k χ_{n,k}(y) (Π_{z_{n,k}} f(z_{n,k}))(y)` is the integrand of the lattice
approximation `S_n f ψ = ∫ ψ · latticeAvg n`. Since the cells form a causal partition of unity,
`latticeAvg` is an average of the values `G_z(y)` over the lattice points `z` at distance
`≤ 8 · 2^{-n}` in the past of `y`. The crude bound `|G_z(y)| ≤ identDom y` for such `z`
(`abs_fnComb_le_identDom_wnear`) gives `|latticeAvg n y| ≤ identDom y` for `n ≥ 1`
(`abs_latticeAvg_le_wnear`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
The dominating bound uses `d(y, z) ≤ 8 · 2^{-n} ≤ 4`.
-/

public section

open Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

theorem identDom_nonneg_wnear (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (y : ParabolicSpace) :
    0 ≤ identDom 𝒯 g γ η Cf CGam y := by
  unfold identDom
  split_ifs
  · exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg S.hCf (by linarith [le_max_right CGam 0]))
        (identDomConst_nonneg 𝒯)) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  · exact le_rfl

/-- For a lattice point `z` in the slab and a point `y` in the support of its cell, the crude bound
`|G_z(y)| ≤ identDom y` holds (for `n ≥ 1`). -/
theorem abs_fnComb_le_identDom_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {n : ℕ} (hn : 1 ≤ n) {k : LatticeIndex}
    {y : ParabolicSpace} (hk : latticeCell n k y ≠ 0) :
    |fnComb 𝒯 g γ (latticePoint n k) (f (latticePoint n k)) y| ≤ identDom 𝒯 g γ η Cf CGam y := by
  obtain ⟨h1, h2, h3⟩ := latticeCell_geometry hk
  set z := latticePoint n k with hzdef
  by_cases hz : z ∈ timeSlab T
  · set s : ℝ := ((2 : ℝ) ^ n)⁻¹ with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s ≤ 1 / 2 := by
      rw [hs]
      have : (2 : ℝ) ≤ 2 ^ n := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
      calc ((2 : ℝ) ^ n)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) this
        _ = 1 / 2 := by norm_num
    have hsq : s ^ 2 ≤ z.1 := sq_le_latticePoint_fst hz.1
    have hzs : s ≤ Real.sqrt z.1 := by
      calc s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs0.le).symm
        _ ≤ Real.sqrt z.1 := Real.sqrt_le_sqrt hsq
    have hw := singularWeight_timeZeroDist_eq hz S.hT
    have hy : y ∈ hairerTimeWindow := by
      refine ⟨by linarith [hz.1], ?_⟩
      have : s ^ 2 ≤ 1 / 4 := by nlinarith
      linarith [hz.2, S.hT]
    have hd : parabolicNorm (y - z) ≤ 8 * singularWeight timeZeroDist z := by
      rw [hw]; linarith
    have hd4 : parabolicNorm (y - z) ≤ 4 := by linarith
    have hb := abs_fnComb_le_of_slab_wnear hg S hz hy hd hd4
    have hy0 : 0 < y.1 := by linarith [hz.1]
    unfold identDom
    simp only [hy0, ↓reduceIte]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    have hK : 0 ≤ Cf * (1 + max CGam 0) * identDomConst 𝒯 :=
      mul_nonneg (mul_nonneg S.hCf (by linarith [le_max_right CGam 0])) (identDomConst_nonneg 𝒯)
    refine mul_le_mul_of_nonneg_left ?_ hK
    rw [hw]
    have hpos : 0 < Real.sqrt (y.1 / 3) := Real.sqrt_pos.2 (by linarith)
    have hle : Real.sqrt (y.1 / 3) ≤ Real.sqrt z.1 := Real.sqrt_le_sqrt (by linarith)
    exact Real.rpow_le_rpow_of_nonpos hpos hle (min_le_right _ _)
  · have hz0 : f z = 0 := S.hf0 z hz
    rw [hz0, fnComb_zero_right, abs_zero]
    exact identDom_nonneg_wnear S y

/-- **Domination**: `|latticeAvg n y| ≤ identDom y` for `n ≥ 1`. -/
theorem abs_latticeAvg_le_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {n : ℕ} (hn : 1 ≤ n) (y : ParabolicSpace) :
    |latticeAvg 𝒯 g γ f n y| ≤ identDom 𝒯 g γ η Cf CGam y :=
  abs_finsum_cell_le fun _ hk => abs_fnComb_le_identDom_wnear hg S hn hk

end Model

end RegularityStructures
