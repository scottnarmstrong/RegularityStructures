/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.WindowAt.SlabNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.Local.Const
public import RegularityStructures.Abstract.Singular.Local.Weight
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Local cell-pair bound, near-pair `Γ`-bounds

For `x` with `64 λ ≤ w_x`, lattice points `x_k` (level `n + 1`) and `x_l` (level `n`) within `2λ` of
`x` and `g` scaled at `x_k` with constant `C_s λ^{-5}`: the pairing
`⟨Π_{x_k}(f(x_k) − Γ_{x_k x_l} f(x_l)), g⟩` is bounded by a constant times
`C_f 2^{-5n} λ^{-5} 2^{-nγ} w_x^{η−γ}`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ η CPi CGam Cf lam T : ℝ}

theorem abs_pairing_regPi_sub_gamma_le_local_win_near {f : ParabolicSpace → ι → ℝ}
    (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hT1 : T ≤ 1)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (hf : M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f) (hCf : 0 ≤ Cf)
    {x : ParabolicSpace} (hlam : 0 < lam) (hx1 : 0 < x.1)
    (hxw : 64 * lam ≤ singularWeight timeZeroDist x) {n : ℕ}
    (hn : 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam) {k l : LatticeIndex}
    (hk : parabolicNorm (latticePoint (n + 1) k - x) ≤ 2 * lam)
    (hl : parabolicNorm (latticePoint n l - x) ≤ 2 * lam)
    (hkl : parabolicNorm (latticePoint (n + 1) k - latticePoint n l) ≤ 12 * ((2 : ℝ) ^ n)⁻¹)
    (hkT : (latticePoint (n + 1) k).1 ≤ T) (hlT : (latticePoint n l).1 ≤ T)
    {Cs : ℝ} (hCs : 0 ≤ Cs) {g : ParabolicSpace → ℝ}
    (hg : IsScaledTest g (latticePoint (n + 1) k) (8 * ((2 : ℝ) ^ (n + 1))⁻¹)
      (Cs * (lam ^ 5)⁻¹)) :
    |parabolicSemigroup.pairing (M.regPi (latticePoint (n + 1) k)
        (f (latticePoint (n + 1) k) -
          M.gammaMap (latticePoint (n + 1) k) (latticePoint n l) (f (latticePoint n l)))) g| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * Cs * localSumConst 𝒯 γ * (2 : ℝ) ^ |η - γ| * Cf *
        ((4 * ((2 : ℝ) ^ n)⁻¹) ^ 5 * (lam ^ 5)⁻¹ * ((2 : ℝ) ^ n)⁻¹ ^ γ *
          singularWeight timeZeroDist x ^ (η - γ)) := by
  set q : ℝ := ((2 : ℝ) ^ n)⁻¹ with hq_def
  have hq : 0 < q := by positivity
  set zk := latticePoint (n + 1) k with hzk
  set zl := latticePoint n l with hzl
  set wx := singularWeight timeZeroDist x with hwx_def
  have hwx : 0 < wx := by linarith
  obtain ⟨hk1, hk2, hk3⟩ := weight_comparable_of_near hlam hx1 hxw hk
  obtain ⟨hl1, hl2, hl3⟩ := weight_comparable_of_near hlam hx1 hxw hl
  have hzkS : zk ∈ timeSlab T := ⟨hk3, hkT⟩
  have hzlS : zl ∈ timeSlab T := ⟨hl3, hlT⟩
  have hρk : 0 < timeZeroDist zk := timeZeroDist_pos_of_mem_timeSlab hzkS
  have hρl : 0 < timeZeroDist zl := timeZeroDist_pos_of_mem_timeSlab hzlS
  set W := min (singularWeight timeZeroDist zl) (singularWeight timeZeroDist zk) with hW_def
  have hW1 : wx / 2 ≤ W := le_min hl1 hk1
  have hW2 : W ≤ 2 * wx := (min_le_right _ _).trans hk2
  have hd : parabolicSemigroup.scaleDist zk zl ≤ W := by
    show parabolicNorm (zk - zl) ≤ W
    linarith
  have hτ : f zk - M.gammaMap zk zl (f zl) ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ (hfT _) ((M.isGradedUnipotent_gammaMap _ _).map_lowerSubspace (hfT _))
  have hmain := M.abs_pairing_regPi_le_of_scaled_slabAt_near hPi hCPi hGam
    (M.hasQualitativeGrowthAt_of_exists hgrowth _) hdeg hzkS.1.le (hzkS.2.trans hT1) hτ hg
  have hR : 8 * ((2 : ℝ) ^ (n + 1))⁻¹ = 4 * q := by
    rw [hq_def, pow_succ]; field_simp; norm_num
  rw [hR] at hmain
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      |(f zk - M.gammaMap zk zl (f zl)) i| * (4 * q) ^ 𝒯.deg i ≤
        Cf * W ^ (η - γ) * q ^ γ * ((12 : ℝ) ^ (γ - 𝒯.deg i) * (4 : ℝ) ^ 𝒯.deg i) := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    have he : 0 < γ - 𝒯.deg i := by linarith
    have hb := hf.2 zl hzlS zk hzkS hρl hρk hd i hi'
    have hd12 : parabolicNorm (zk - zl) ^ (γ - 𝒯.deg i) ≤ (12 * q) ^ (γ - 𝒯.deg i) :=
      Real.rpow_le_rpow (parabolicNorm_nonneg _) hkl he.le
    have hWp : 0 ≤ W ^ (η - γ) := Real.rpow_nonneg (by linarith) _
    have hb' : |(f zk - M.gammaMap zk zl (f zl)) i| ≤ Cf * (12 * q) ^ (γ - 𝒯.deg i) *
        W ^ (η - γ) := hb.trans (by
      show Cf * parabolicNorm (zk - zl) ^ (γ - 𝒯.deg i) * W ^ (η - γ) ≤ _
      gcongr)
    calc |(f zk - M.gammaMap zk zl (f zl)) i| * (4 * q) ^ 𝒯.deg i
        ≤ Cf * (12 * q) ^ (γ - 𝒯.deg i) * W ^ (η - γ) * (4 * q) ^ 𝒯.deg i :=
          mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg (by positivity) _)
      _ = Cf * W ^ (η - γ) * (q ^ (γ - 𝒯.deg i) * q ^ 𝒯.deg i) *
            ((12 : ℝ) ^ (γ - 𝒯.deg i) * (4 : ℝ) ^ 𝒯.deg i) := by
          rw [Real.mul_rpow (by norm_num) hq.le, Real.mul_rpow (by norm_num) hq.le]; ring
      _ = _ := by rw [← Real.rpow_add hq]; congr 3; ring
  have hsum : ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      |(f zk - M.gammaMap zk zl (f zl)) i| * (4 * q) ^ 𝒯.deg i ≤
        Cf * ((2 : ℝ) ^ |η - γ| * wx ^ (η - γ)) * q ^ γ * localSumConst 𝒯 γ := by
    have hWp := rpow_le_two_pow_abs_mul hwx hW1 hW2 (η - γ)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    unfold localSumConst
    gcongr
  have hA : 0 ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (Cs * (lam ^ 5)⁻¹ * (4 * q) ^ 5) := by
    have := r4ModelConst_nonneg 𝒯 hdeg
    positivity
  refine hmain.trans ((mul_le_mul_of_nonneg_left hsum hA).trans (le_of_eq ?_))
  ring

end RegularityStructures.Model

end
