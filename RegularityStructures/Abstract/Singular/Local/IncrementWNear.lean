/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Local.PairWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.LatticeApprox.TelescopeW
public import RegularityStructures.Abstract.Singular.Local.Const
public import RegularityStructures.Abstract.Singular.Local.Increment
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Local increment bound for the lattice approximations, near-pair `Γ`-bounds

The increment bound [Hai14, (7.5)]: for `x` in the slab with `64 λ ≤ w_x` and `8 · 2^{-n} ≤ λ`, the
lattice approximations of `f` against `φ^λ_x` at levels `n + 1` and `n` differ by at most
`C K₀ C_f 2^{-nγ} w_x^{η−γ}`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

open scoped ContDiff

namespace RegularityStructures

private theorem parabolicNorm_sub_le_trans (a b c : ParabolicSpace) :
    parabolicNorm (a - c) ≤ parabolicNorm (a - b) + parabolicNorm (b - c) := by
  have : a - c = (a - b) + (b - c) := by abel
  rw [this]
  exact parabolicNorm_add_le _ _

private theorem three_le_of_eight_mul_inv_le {lam : ℝ} (hl1 : lam ≤ 1) {n : ℕ}
    (hn : 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam) : 3 ≤ n := by
  by_contra h
  push Not at h
  interval_cases n <;> norm_num at hn <;> linarith

private theorem eight_le_two_pow_mul {lam : ℝ} {n : ℕ} (hn : 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam) :
    8 ≤ (2 : ℝ) ^ n * lam := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have := mul_le_mul_of_nonneg_left hn h2.le
  have e : (2 : ℝ) ^ n * (8 * ((2 : ℝ) ^ n)⁻¹) = 8 := by field_simp
  linarith

private theorem eight_mul_two_pow_succ_inv_le {n : ℕ} :
    8 * ((2 : ℝ) ^ (n + 1))⁻¹ ≤ 8 * ((2 : ℝ) ^ n)⁻¹ := by
  rw [pow_succ]
  have : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h : ((2 : ℝ) ^ n * 2)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ :=
    inv_anti₀ this (by linarith)
  linarith

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- Hairer (arXiv:1303.5113v4), (7.5): increment bound for the lattice approximations. -/
theorem exists_abs_latticeApprox_succ_sub_le_of_nonneg_win_near (𝒯 : RegularityStructure ι) {γ : ℝ} (η : ℝ)
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
      8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam →
      |M.latticeApprox f (rescaledTestFunction φ lam x) (n + 1) -
          M.latticeApprox f (rescaledTestFunction φ lam x) n| ≤
        C * (max 1 CGam * CPi) * Cf * ((2 : ℝ) ^ n)⁻¹ ^ γ *
          singularWeight timeZeroDist x ^ (η - γ) := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_isScaledTest_rescaledTestFunction_mul_latticeCell_mul
  refine ⟨24057 * (290 * 26 ^ 3) * 4 ^ 5 * r4ModelConst 𝒯 γ * Cs * localSumConst 𝒯 γ *
    (2 : ℝ) ^ |η - γ|, ?_, fun M CPi CGam Cf f T φ lam x n hPi hCPi hGam hgrowth hT1 hfT hf hCf hφ hlam hl1 hx
      hxw hφT hn => ?_⟩
  · have := r4ModelConst_nonneg 𝒯 hdeg
    have := localSumConst_nonneg 𝒯 γ
    positivity
  set ψ := rescaledTestFunction φ lam x with hψ_def
  set q : ℝ := ((2 : ℝ) ^ n)⁻¹ with hq_def
  have hq : 0 < q := by positivity
  have hn3 := three_le_of_eight_mul_inv_le hl1 hn
  have hn' : 8 * ((2 : ℝ) ^ (n + 1))⁻¹ ≤ lam := eight_mul_two_pow_succ_inv_le.trans hn
  have hψs : ContDiff ℝ ∞ ψ := contDiff_rescaledTestFunction hφ.1 lam x
  have hs' : ∀ k w, ψ w * latticeCell (n + 1) k w ≠ 0 →
      k ∈ latticeBox (n + 1) x ((2 * lam) ^ 2) (2 * lam) := fun k w h =>
    mem_latticeBox_of_rescaledTestFunction_mul_latticeCell_ne_zero hφ.2.1 hlam hn' h
  have hs : ∀ k w, ψ w * latticeCell n k w ≠ 0 → k ∈ latticeBox n x ((2 * lam) ^ 2) (2 * lam) :=
    fun k w h => mem_latticeBox_of_rescaledTestFunction_mul_latticeCell_ne_zero hφ.2.1 hlam hn h
  rw [M.latticeApprox_succ_sub_eq_win hψs hfT hgrowth hdeg hn3 hs' hs]
  have hP : 0 ≤ r4ModelConst 𝒯 γ := r4ModelConst_nonneg 𝒯 hdeg
  have hSum := localSumConst_nonneg 𝒯 γ
  have hwx : 0 < singularWeight timeZeroDist x := by linarith
  -- the bound for one active pair
  set B : ℝ := r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * Cs * localSumConst 𝒯 γ *
    (2 : ℝ) ^ |η - γ| * Cf * ((4 * q) ^ 5 * (lam ^ 5)⁻¹ * q ^ γ *
      singularWeight timeZeroDist x ^ (η - γ)) with hB_def
  have hB : 0 ≤ B := by positivity
  have hcount := abs_sum_sum_le_of_active
    (latticeBox (n + 1) x ((2 * lam) ^ 2) (2 * lam)) (latticeBox n x ((2 * lam) ^ 2) (2 * lam))
    (fun k l => parabolicSemigroup.pairing
        (M.regPi (latticePoint (n + 1) k) (f (latticePoint (n + 1) k) -
          M.gammaMap (latticePoint (n + 1) k) (latticePoint n l) (f (latticePoint n l))))
        (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w))
    (fun k => latticeBox n (latticePoint (n + 1) k) ((12 * q) ^ 2) (12 * q))
    (N := 290 * 26 ^ 3) (B := B) hB (fun k _ => card_latticeBox_near_le n _) ?_
  · refine hcount.trans ?_
    have hu := eight_le_two_pow_mul hn
    have hcard := card_latticeBox_succ_le (x := x) hu
    have hN : (0 : ℝ) ≤ 290 * 26 ^ 3 := by norm_num
    have key : ((2 : ℝ) ^ n * lam) ^ 5 * ((4 * q) ^ 5 * (lam ^ 5)⁻¹) = 4 ^ 5 := by
      rw [hq_def]; field_simp
    calc _ ≤ 24057 * ((2 : ℝ) ^ n * lam) ^ 5 * (290 * 26 ^ 3 * B) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by
          rw [hB_def]
          calc _ = 24057 * (290 * 26 ^ 3) * (r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * Cs *
                localSumConst 𝒯 γ * (2 : ℝ) ^ |η - γ| * Cf) * q ^ γ *
                singularWeight timeZeroDist x ^ (η - γ) *
                (((2 : ℝ) ^ n * lam) ^ 5 * ((4 * q) ^ 5 * (lam ^ 5)⁻¹)) := by ring
            _ = _ := by rw [key]; ring
  · intro k _ l _ hne
    have hg0 : ∃ w, ψ w * latticeCell (n + 1) k w * latticeCell n l w ≠ 0 := by
      by_contra hno
      push Not at hno
      apply hne
      have : (fun w => ψ w * latticeCell (n + 1) k w * latticeCell n l w) = fun _ => 0 :=
        funext hno
      rw [this]
      exact pairing_zero_test _ _
    obtain ⟨w, hw⟩ := hg0
    obtain ⟨hA, h3⟩ := mul_ne_zero_iff.1 hw
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hA
    have hψw : parabolicNorm (w - x) ≤ lam := by
      by_contra hc
      exact h1 (rescaledTestFunction_eq_zero hφ.2.1 hlam (not_le.1 hc))
    have hwT : w.1 ≤ T := by
      by_contra hc
      exact h1 (hφT w (not_le.1 hc))
    have hwk := parabolicNorm_sub_latticePoint_le h2
    have hwl := parabolicNorm_sub_latticePoint_le h3
    have hkw := parabolicNorm_sub_comm (latticePoint (n + 1) k) w
    have hlw := parabolicNorm_sub_comm (latticePoint n l) w
    have hk8 : 8 * ((2 : ℝ) ^ (n + 1))⁻¹ = 4 * q := by
      rw [hq_def, pow_succ]; field_simp; norm_num
    have hk : parabolicNorm (latticePoint (n + 1) k - x) ≤ 2 * lam := by
      have := parabolicNorm_sub_le_trans (latticePoint (n + 1) k) w x
      linarith
    have hl : parabolicNorm (latticePoint n l - x) ≤ 2 * lam := by
      have := parabolicNorm_sub_le_trans (latticePoint n l) w x
      linarith
    have hkl : parabolicNorm (latticePoint (n + 1) k - latticePoint n l) ≤ 12 * q := by
      have := parabolicNorm_sub_le_trans (latticePoint (n + 1) k) w (latticePoint n l)
      linarith
    refine ⟨mem_latticeBox_of_parabolicNorm_le ?_, ?_⟩
    · rw [parabolicNorm_sub_comm]; exact hkl
    · exact M.abs_pairing_regPi_sub_gamma_le_local_win_near hPi hCPi hGam hgrowth hT1 hdeg hfT hf hCf hlam hx.1 hxw hn
        hk hl hkl (by linarith [(latticeCell_ne_zero h2).1.1]) (by linarith
          [(latticeCell_ne_zero h3).1.1]) hCs0.le (hCs hφ hlam hl1 x n hn k l)

end Model

end RegularityStructures

end
