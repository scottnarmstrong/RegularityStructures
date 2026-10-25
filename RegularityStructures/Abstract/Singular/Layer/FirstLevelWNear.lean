/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Layer.SupBoundWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Layer.BoxSums
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# First-level bound for the lattice approximations, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, the level-`n` lattice approximation of `f` against
`φ^λ_x` (`φ ∈ testFunctionClass 4`, `0 < λ ≤ 1`) is bounded by `C K₀ C_f λ^{α ∧ η}`,
`K₀ = max(1, C_Γ) C_Π`, at the first level `32 ≤ λ 2^n ≤ 64`, for models whose `Γ`-bounds hold only
for near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place
of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem rpow_scale_le {r lam : ℝ} (hlam : 0 < lam) (hr1 : lam / 64 ≤ r) (hr2 : r ≤ lam)
    (m : ℝ) : r ^ m ≤ (64 : ℝ) ^ |m| * lam ^ m := by
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have h64 : (1 : ℝ) ≤ 64 ^ |m| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  rcases le_or_gt 0 m with hm | hm
  · calc r ^ m ≤ lam ^ m := Real.rpow_le_rpow hr.le hr2 hm
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hlam.le _) h64
  · calc r ^ m ≤ (lam / 64) ^ m := Real.rpow_le_rpow_of_nonpos (by positivity) hr1 hm.le
      _ = (64 : ℝ) ^ |m| * lam ^ m := by
        rw [Real.div_rpow hlam.le (by norm_num), abs_of_neg hm, Real.rpow_neg (by norm_num),
          div_eq_mul_inv, mul_comm, ← inv_inv ((64 : ℝ) ^ m)]

theorem exists_abs_layerApprox_le_win_near (𝒯 : RegularityStructure ι) (γ α η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
      {Cf CPi CGam T : ℝ}, LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {φ : ParabolicSpace → ℝ}, φ ∈ testFunctionClass 4 → ∀ {lam : ℝ}, 0 < lam → lam ≤ 1 →
      ∀ (x : ParabolicSpace) {n : ℕ}, 32 ≤ lam * 2 ^ n → lam * 2 ^ n ≤ 64 →
      |M.latticeApprox f (rescaledTestFunction φ lam x) n| ≤
        C * (max 1 CGam * CPi) * Cf * lam ^ (min α η) := by
  obtain ⟨C₀, hC₀, hsup⟩ := exists_abs_pairing_regPi_lattice_le_win_near 𝒯 γ
  obtain ⟨C₃, hC₃, h3a⟩ := exists_isScaledTest_rescaledTestFunction_mul_latticeCell
  refine ⟨10370 * 146 ^ 3 * (C₀ * C₃ * (64 : ℝ) ^ |min α η|), by positivity, ?_⟩
  intro M f Cf CPi CGam T S φ hφ lam hlam hlam1 x n hn hn'
  set r : ℝ := ((2 : ℝ) ^ n)⁻¹ with hr_def
  set m : ℝ := min α η with hm_def
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hr : 0 < r := by positivity
  have hrΛ : r * 2 ^ n = 1 := by rw [hr_def]; field_simp
  have hr1 : r ≤ lam / 32 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hr2 : lam / 64 ≤ r := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    have h2' : (2 : ℝ) ^ n ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hn8 : 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam := by rw [← hr_def]; linarith
  have hψ0 : ∀ w, lam < parabolicNorm (w - x) → rescaledTestFunction φ lam x w = 0 :=
    fun w hw => rescaledTestFunction_eq_zero hφ.2.1 hlam hw
  have hs : ∀ k w, rescaledTestFunction φ lam x w * latticeCell n k w ≠ 0 →
      k ∈ latticeBox n x ((lam + 8 * ((2 : ℝ) ^ n)⁻¹) ^ 2) (lam + 8 * ((2 : ℝ) ^ n)⁻¹) :=
    fun k w h => Layer.mem_latticeBox_of_support hψ0 n k w h
  rw [M.latticeApprox_eq_sum hs]
  set s := latticeBox n x ((lam + 8 * ((2 : ℝ) ^ n)⁻¹) ^ 2) (lam + 8 * ((2 : ℝ) ^ n)⁻¹) with hs_def
  set B : ℝ := C₀ * (max 1 CGam * CPi) * Cf * (C₃ * (lam ^ 5)⁻¹) * r ^ (5 + m) with hB
  have hterm : ∀ k ∈ s, |parabolicSemigroup.pairing (M.regPi (latticePoint n k)
      (f (latticePoint n k))) (fun w => rescaledTestFunction φ lam x w * latticeCell n k w)| ≤ B :=
    fun k _ => hsup S hn3 (h3a hφ hlam hlam1 x n hn8 k)
  have hcard : (s.card : ℝ) ≤ 10370 * 146 ^ 3 := by
    have h := card_latticeBox_le (n := n) (x := x) (rt := (lam + 8 * ((2 : ℝ) ^ n)⁻¹) ^ 2)
      (rs := lam + 8 * ((2 : ℝ) ^ n)⁻¹) (by positivity) (by positivity)
    refine h.trans ?_
    have e1 : (2 : ℝ) ^ n * (lam + 8 * ((2 : ℝ) ^ n)⁻¹) = lam * 2 ^ n + 8 := by
      field_simp
    have e2 : (4 : ℝ) ^ n * (lam + 8 * ((2 : ℝ) ^ n)⁻¹) ^ 2 = (lam * 2 ^ n + 8) ^ 2 := by
      rw [← e1, show (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      ring
    have e3 : 2 * (4 : ℝ) ^ n * (lam + 8 * ((2 : ℝ) ^ n)⁻¹) ^ 2 + 2 ≤ 10370 := by
      rw [mul_assoc, e2]; nlinarith
    have e4 : 2 * (2 : ℝ) ^ n * (lam + 8 * ((2 : ℝ) ^ n)⁻¹) + 2 ≤ 146 := by
      rw [mul_assoc, e1]; nlinarith
    have h0 : 0 ≤ 2 * (2 : ℝ) ^ n * (lam + 8 * ((2 : ℝ) ^ n)⁻¹) + 2 := by positivity
    calc _ ≤ 10370 * (2 * (2 : ℝ) ^ n * (lam + 8 * ((2 : ℝ) ^ n)⁻¹) + 2) ^ 3 := by
          refine mul_le_mul e3 le_rfl (by positivity) (by norm_num)
      _ ≤ 10370 * 146 ^ 3 := by gcongr
  have hsum : |∑ k ∈ s, parabolicSemigroup.pairing (M.regPi (latticePoint n k)
      (f (latticePoint n k))) (fun w => rescaledTestFunction φ lam x w * latticeCell n k w)| ≤
      s.card * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  refine hsum.trans ?_
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hCf := S.hCf
  have hB0 : 0 ≤ B := by
    have := Real.rpow_nonneg hr.le (5 + m)
    rw [hB]; positivity
  have hBle : B ≤ C₀ * C₃ * (64 : ℝ) ^ |m| * ((max 1 CGam * CPi) * Cf * lam ^ m) := by
    have e5 : (lam ^ 5)⁻¹ * r ^ (5 + m) ≤ r ^ m := by
      rw [Real.rpow_add hr, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have : r ^ 5 ≤ lam ^ 5 := pow_le_pow_left₀ hr.le (by linarith) 5
      have hl5 : 0 < lam ^ 5 := by positivity
      calc (lam ^ 5)⁻¹ * (r ^ 5 * r ^ m) = ((lam ^ 5)⁻¹ * r ^ 5) * r ^ m := by ring
        _ ≤ 1 * r ^ m := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hr.le _)
            rw [inv_mul_le_iff₀ hl5]; linarith
        _ = _ := one_mul _
    have e6 := rpow_scale_le hlam hr2 (by linarith) m
    have hP : 0 ≤ C₀ * (max 1 CGam * CPi) * Cf * C₃ := by positivity
    calc B = (C₀ * (max 1 CGam * CPi) * Cf * C₃) * ((lam ^ 5)⁻¹ * r ^ (5 + m)) := by
          rw [hB]; ring
      _ ≤ (C₀ * (max 1 CGam * CPi) * Cf * C₃) * ((64 : ℝ) ^ |m| * lam ^ m) :=
          mul_le_mul_of_nonneg_left (e5.trans e6) hP
      _ = _ := by ring
  calc (s.card : ℝ) * B ≤ (10370 * 146 ^ 3) * B := mul_le_mul_of_nonneg_right hcard hB0
    _ ≤ (10370 * 146 ^ 3) * (C₀ * C₃ * (64 : ℝ) ^ |m| * ((max 1 CGam * CPi) * Cf * lam ^ m)) :=
        mul_le_mul_of_nonneg_left hBle (by norm_num)
    _ = _ := by ring

end RegularityStructures

end
