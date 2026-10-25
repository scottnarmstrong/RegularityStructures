/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Local.IncrementWNear
public import RegularityStructures.Abstract.Singular.WindowAt.SlabNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.LatticeApprox.ComparisonW
public import RegularityStructures.Abstract.Singular.Local.Const
public import RegularityStructures.Abstract.Singular.Local.FirstLevel
public import RegularityStructures.Abstract.Singular.Local.Weight
public import RegularityStructures.Abstract.Singular.WindowAt.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The first level of the lattice approximation, near-pair `Γ`-bounds

[Hai14, (7.3)]: for `ψ = φ^λ_x` with `x` in the time slab, `64 λ ≤ w(x)` and
`8 · 2^{-n} ≤ λ ≤ 16 · 2^{-n}`, `|S_n f ψ - ⟨Π_x f(x), ψ⟩| ≤ C K₀ C_f λ^γ w(x)^{η-γ}` with
`K₀ = max 1 CGam * CPi` (`exists_abs_latticeApprox_sub_pairing_le_of_nonneg_win_near`). The model
bounds are assumed on `hairerTimeWindow`, together with a qualitative growth model, for models whose
`Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem parabolicNorm_sub_le_trans' (a b c : ParabolicSpace) :
    parabolicNorm (a - c) ≤ parabolicNorm (a - b) + parabolicNorm (b - c) := by
  have : a - c = (a - b) + (b - c) := by abel
  rw [this]
  exact parabolicNorm_add_le _ _

private theorem three_le_of_eight_mul_inv_le' {lam : ℝ} (hl1 : lam ≤ 1) {n : ℕ}
    (hn : 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam) : 3 ≤ n := by
  by_contra h
  push Not at h
  interval_cases n <;> norm_num at hn <;> linarith

namespace Model

variable {𝒯 : RegularityStructure ι} (M : Model 𝒯 parabolicSemigroup)
  {γ η CPi CGam Cf lam T : ℝ}

theorem abs_pairing_regPi_sub_gamma_le_first_win_near {f : ParabolicSpace → ι → ℝ}
    (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hT1 : T ≤ 1)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (hf : M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f) (hCf : 0 ≤ Cf)
    {x : ParabolicSpace} (hlam : 0 < lam) (hx : x ∈ timeSlab T)
    (hxw : 64 * lam ≤ singularWeight timeZeroDist x) {n : ℕ}
    (hn : 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam) (hn16 : lam ≤ 16 * ((2 : ℝ) ^ n)⁻¹) {k : LatticeIndex}
    (hk : parabolicNorm (latticePoint n k - x) ≤ 2 * lam)
    (hkT : (latticePoint n k).1 ≤ T) {Cs : ℝ} (hCs : 0 ≤ Cs) {g : ParabolicSpace → ℝ}
    (hg : IsScaledTest g (latticePoint n k) (8 * ((2 : ℝ) ^ n)⁻¹) (Cs * (lam ^ 5)⁻¹)) :
    |parabolicSemigroup.pairing (M.regPi (latticePoint n k)
        (f (latticePoint n k) - M.gammaMap (latticePoint n k) x (f x))) g| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * Cs * firstLevelSumConst 𝒯 γ *
        (2 : ℝ) ^ |η - γ| * Cf * (lam ^ γ * singularWeight timeZeroDist x ^ (η - γ)) := by
  set q : ℝ := ((2 : ℝ) ^ n)⁻¹ with hq_def
  have hq : 0 < q := by positivity
  set zk := latticePoint n k with hzk
  set wx := singularWeight timeZeroDist x with hwx_def
  have hwx : 0 < wx := by linarith
  obtain ⟨hk1, hk2, hk3⟩ := weight_comparable_of_near hlam hx.1 hxw hk
  have hzkS : zk ∈ timeSlab T := ⟨hk3, hkT⟩
  have hρk : 0 < timeZeroDist zk := timeZeroDist_pos_of_mem_timeSlab hzkS
  have hρx : 0 < timeZeroDist x := timeZeroDist_pos_of_mem_timeSlab hx
  set W := min (singularWeight timeZeroDist x) (singularWeight timeZeroDist zk) with hW_def
  have hW1 : wx / 2 ≤ W := le_min (by linarith) hk1
  have hW2 : W ≤ 2 * wx := (min_le_left _ _).trans (by linarith)
  have hd : parabolicSemigroup.scaleDist zk x ≤ W := by
    show parabolicNorm (zk - x) ≤ W
    linarith
  have hτ : f zk - M.gammaMap zk x (f x) ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ (hfT _) ((M.isGradedUnipotent_gammaMap _ _).map_lowerSubspace (hfT _))
  have hmain := M.abs_pairing_regPi_le_of_scaled_slabAt_near hPi hCPi hGam
    (M.hasQualitativeGrowthAt_of_exists hgrowth _) hdeg hzkS.1.le (hzkS.2.trans hT1) hτ hg
  have hR1 : lam / 2 ≤ 8 * q := by linarith
  have hR2 : 8 * q ≤ 2 * lam := by linarith
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      |(f zk - M.gammaMap zk x (f x)) i| * (8 * q) ^ 𝒯.deg i ≤
        Cf * W ^ (η - γ) * lam ^ γ * ((2 : ℝ) ^ (γ - 𝒯.deg i) * (2 : ℝ) ^ |𝒯.deg i|) := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    have he : 0 < γ - 𝒯.deg i := by linarith
    have hb := hf.2 x hx zk hzkS hρx hρk hd i hi'
    have hd2 : parabolicNorm (zk - x) ^ (γ - 𝒯.deg i) ≤ (2 * lam) ^ (γ - 𝒯.deg i) :=
      Real.rpow_le_rpow (parabolicNorm_nonneg _) hk he.le
    have hWp : 0 ≤ W ^ (η - γ) := Real.rpow_nonneg (by linarith) _
    have hb' : |(f zk - M.gammaMap zk x (f x)) i| ≤ Cf * (2 * lam) ^ (γ - 𝒯.deg i) *
        W ^ (η - γ) := hb.trans (by
      show Cf * parabolicNorm (zk - x) ^ (γ - 𝒯.deg i) * W ^ (η - γ) ≤ _
      gcongr)
    have hRp := rpow_le_two_pow_abs_mul hlam hR1 hR2 (𝒯.deg i)
    calc |(f zk - M.gammaMap zk x (f x)) i| * (8 * q) ^ 𝒯.deg i
        ≤ Cf * (2 * lam) ^ (γ - 𝒯.deg i) * W ^ (η - γ) *
            ((2 : ℝ) ^ |𝒯.deg i| * lam ^ 𝒯.deg i) :=
          mul_le_mul hb' hRp (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = Cf * W ^ (η - γ) * (lam ^ (γ - 𝒯.deg i) * lam ^ 𝒯.deg i) *
            ((2 : ℝ) ^ (γ - 𝒯.deg i) * (2 : ℝ) ^ |𝒯.deg i|) := by
          rw [Real.mul_rpow (by norm_num) hlam.le]; ring
      _ = _ := by rw [← Real.rpow_add hlam]; congr 3; ring
  have hsum : ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      |(f zk - M.gammaMap zk x (f x)) i| * (8 * q) ^ 𝒯.deg i ≤
        Cf * ((2 : ℝ) ^ |η - γ| * wx ^ (η - γ)) * lam ^ γ * firstLevelSumConst 𝒯 γ := by
    have hWp := rpow_le_two_pow_abs_mul hwx hW1 hW2 (η - γ)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    unfold firstLevelSumConst
    gcongr
  have hP : 0 ≤ r4ModelConst 𝒯 γ := r4ModelConst_nonneg 𝒯 hdeg
  have hA : 0 ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (Cs * (lam ^ 5)⁻¹ * (8 * q) ^ 5) := by
    positivity
  have hAR : Cs * (lam ^ 5)⁻¹ * (8 * q) ^ 5 ≤ Cs := by
    have h5 : (8 * q) ^ 5 ≤ lam ^ 5 := pow_le_pow_left₀ (by positivity) hn 5
    have : (lam ^ 5)⁻¹ * (8 * q) ^ 5 ≤ 1 := by
      rw [inv_mul_le_iff₀ (by positivity)]; linarith
    nlinarith
  have hB : 0 ≤ Cf * ((2 : ℝ) ^ |η - γ| * wx ^ (η - γ)) * lam ^ γ * firstLevelSumConst 𝒯 γ := by
    have := firstLevelSumConst_nonneg 𝒯 γ
    positivity
  have hK : 0 ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) := by positivity
  calc _ ≤ _ := hmain
    _ ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (Cs * (lam ^ 5)⁻¹ * (8 * q) ^ 5) *
        (Cf * ((2 : ℝ) ^ |η - γ| * wx ^ (η - γ)) * lam ^ γ * firstLevelSumConst 𝒯 γ) :=
        mul_le_mul_of_nonneg_left hsum hA
    _ ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * Cs *
        (Cf * ((2 : ℝ) ^ |η - γ| * wx ^ (η - γ)) * lam ^ γ * firstLevelSumConst 𝒯 γ) := by
        refine mul_le_mul_of_nonneg_right ?_ hB
        exact mul_le_mul_of_nonneg_left hAR hK
    _ = _ := by ring

/-- Hairer (arXiv:1303.5113v4), (7.3): comparison of the first lattice level with `⟨Π_x f(x), ψ⟩`. -/
theorem exists_abs_latticeApprox_sub_pairing_le_of_nonneg_win_near (𝒯 : RegularityStructure ι) {γ : ℝ} (η : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam Cf : ℝ}
      {f : ParabolicSpace → ι → ℝ} {T : ℝ} {φ : ParabolicSpace → ℝ} {lam : ℝ}
      {x : ParabolicSpace} {n : ℕ},
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi → M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      T ≤ 1 →
      (∀ z, f z ∈ lowerSubspace 𝒯.deg γ) →
      M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f → 0 ≤ Cf →
      φ ∈ testFunctionClass 4 → 0 < lam → lam ≤ 1 → x ∈ timeSlab T →
      64 * lam ≤ singularWeight timeZeroDist x →
      (∀ w : ParabolicSpace, T < w.1 → rescaledTestFunction φ lam x w = 0) →
      8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam → lam ≤ 16 * ((2 : ℝ) ^ n)⁻¹ →
      |M.latticeApprox f (rescaledTestFunction φ lam x) n -
          parabolicSemigroup.pairing (M.regPi x (f x)) (rescaledTestFunction φ lam x)| ≤
        C * (max 1 CGam * CPi) * Cf * lam ^ γ * singularWeight timeZeroDist x ^ (η - γ) := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_isScaledTest_rescaledTestFunction_mul_latticeCell
  refine ⟨2050 * 66 ^ 3 * r4ModelConst 𝒯 γ * Cs * firstLevelSumConst 𝒯 γ *
    (2 : ℝ) ^ |η - γ|, ?_, fun M CPi CGam Cf f T φ lam x n hPi hCPi hGam hgrowth hT1 hfT hf hCf hφ hlam hl1
      hx hxw hφT hn hn16 => ?_⟩
  · have := r4ModelConst_nonneg 𝒯 hdeg
    have := firstLevelSumConst_nonneg 𝒯 γ
    positivity
  set ψ := rescaledTestFunction φ lam x with hψ_def
  have hq : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have hn3 := three_le_of_eight_mul_inv_le' hl1 hn
  have hψs : ContDiff ℝ ∞ ψ := contDiff_rescaledTestFunction hφ.1 lam x
  have hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ latticeBox n x ((2 * lam) ^ 2) (2 * lam) :=
    fun k w h => mem_latticeBox_of_rescaledTestFunction_mul_latticeCell_ne_zero hφ.2.1 hlam hn h
  have hsupp : ∀ w, lam < parabolicNorm (w - x) → ψ w = 0 := fun w hw =>
    rescaledTestFunction_eq_zero hφ.2.1 hlam hw
  rw [M.latticeApprox_sub_pairing_eq_win hψs hfT hlam hl1 hsupp hgrowth hdeg (hfT x) hn3 hs]
  have hP : 0 ≤ r4ModelConst 𝒯 γ := r4ModelConst_nonneg 𝒯 hdeg
  have hSum := firstLevelSumConst_nonneg 𝒯 γ
  have hwx : 0 < singularWeight timeZeroDist x := by linarith
  set B : ℝ := r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * Cs * firstLevelSumConst 𝒯 γ *
    (2 : ℝ) ^ |η - γ| * Cf * (lam ^ γ * singularWeight timeZeroDist x ^ (η - γ)) with hB_def
  have hB : 0 ≤ B := by positivity
  have hterm : ∀ k ∈ latticeBox n x ((2 * lam) ^ 2) (2 * lam),
      |parabolicSemigroup.pairing
        (M.regPi (latticePoint n k) (f (latticePoint n k) - M.gammaMap (latticePoint n k) x (f x)))
        (fun w => ψ w * latticeCell n k w)| ≤ B := by
    intro k _
    by_cases hw : ∃ w, ψ w * latticeCell n k w ≠ 0
    · obtain ⟨w, hw⟩ := hw
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hw
      have hψw : parabolicNorm (w - x) ≤ lam := by
        by_contra hc
        exact h1 (hsupp w (not_le.1 hc))
      have hwT : w.1 ≤ T := by
        by_contra hc
        exact h1 (hφT w (not_le.1 hc))
      have hwk := parabolicNorm_sub_latticePoint_le h2
      have hkw := parabolicNorm_sub_comm (latticePoint n k) w
      have hk : parabolicNorm (latticePoint n k - x) ≤ 2 * lam := by
        have := parabolicNorm_sub_le_trans' (latticePoint n k) w x
        linarith
      exact M.abs_pairing_regPi_sub_gamma_le_first_win_near hPi hCPi hGam hgrowth hT1 hdeg hfT hf hCf hlam hx hxw hn
        hn16 hk (by linarith [(latticeCell_ne_zero h2).1.1]) hCs0.le (hCs hφ hlam hl1 x n hn k)
    · push Not at hw
      have : (fun w => ψ w * latticeCell n k w) = fun _ => 0 := funext hw
      rw [this, pairing_zero_test, abs_zero]
      exact hB
  have hu : (2 : ℝ) ^ n * lam ≤ 16 := by
    have := mul_le_mul_of_nonneg_left hn16 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)
    have e : (2 : ℝ) ^ n * (16 * ((2 : ℝ) ^ n)⁻¹) = 16 := by field_simp
    linarith
  have hcard := card_latticeBox_two_mul_le (n := n) (x := x) hlam hu
  calc _ ≤ ∑ k ∈ latticeBox n x ((2 * lam) ^ 2) (2 * lam), |parabolicSemigroup.pairing
        (M.regPi (latticePoint n k) (f (latticePoint n k) - M.gammaMap (latticePoint n k) x (f x)))
        (fun w => ψ w * latticeCell n k w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ latticeBox n x ((2 * lam) ^ 2) (2 * lam), B := Finset.sum_le_sum hterm
    _ = (latticeBox n x ((2 * lam) ^ 2) (2 * lam)).card * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2050 * 66 ^ 3) * B := mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by rw [hB_def]; ring

end Model

end RegularityStructures

end
