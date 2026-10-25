/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Layer.Setting
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Model bound at lattice points, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, for `q ≥ 3` and a test function `g` scaled at the
level-`q` lattice point `x_k` with radius `8 · 2^{-q}` and constant `A`:
`|⟨Π_{x_k} f(x_k), g⟩| ≤ C K₀ C_f A 2^{-q(5 + α ∧ η)}`, for models whose `Γ`-bounds hold only for
near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

private theorem rpow_mul_rpow_min {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) {m η d : ℝ}
    (hd : m ≤ d) (hm : m ≤ η) :
    u ^ (min (η - d) 0) * u ^ d ≤ u ^ m := by
  rw [← Real.rpow_add hu]
  refine Real.rpow_le_rpow_of_exponent_ge hu hu1 ?_
  rcases le_total (η - d) 0 with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem exists_abs_pairing_regPi_lattice_le_win_near (𝒯 : RegularityStructure ι) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
      {η α Cf CPi CGam T : ℝ}, LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {q : ℕ}, 3 ≤ q →
      ∀ {k : LatticeIndex} {g : ParabolicSpace → ℝ} {A : ℝ},
      IsScaledTest g (latticePoint q k) (8 * ((2 : ℝ) ^ q)⁻¹) A →
      |parabolicSemigroup.pairing (M.regPi (latticePoint q k) (f (latticePoint q k))) g| ≤
        C * (max 1 CGam * CPi) * Cf * A * (((2 : ℝ) ^ q)⁻¹) ^ (5 + min α η) := by
  set D8 : ℝ := ∑ i, (8 : ℝ) ^ 𝒯.deg i with hD8
  refine ⟨|r4ModelConst 𝒯 γ| * 8 ^ 5 * D8, by positivity, fun {M f η α Cf CPi CGam T} S q hq k g A hg => ?_⟩
  set u : ℝ := ((2 : ℝ) ^ q)⁻¹ with hu_def
  have hu : 0 < u := by positivity
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  set z := latticePoint q k with hz
  have hK0 : 0 ≤ max 1 CGam * CPi :=
    S.hK0
  have hA := hg.const_pos
  have hRHS : 0 ≤ |r4ModelConst 𝒯 γ| * 8 ^ 5 * D8 * (max 1 CGam * CPi) * Cf * A * u ^ (5 + min α η) := by
    have hD : 0 ≤ D8 := Finset.sum_nonneg fun i _ => by positivity
    have hr := Real.rpow_nonneg hu.le (5 + min α η)
    have hCf := S.hCf
    positivity
  by_cases hfz : f z = 0
  · rw [hfz, pairing_regPi_zero_eq]; simpa using hRHS
  · have hslab : z ∈ timeSlab T := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hfz
      exact S.mem_timeSlab_of_ne_zero hi
    have hw : u ≤ singularWeight timeZeroDist z := Layer.inv_two_pow_le_singularWeight hslab.1
    have hρ : 0 < timeZeroDist z := timeZeroDist_pos_of_mem_timeSlab hslab
    have hmain := S.abs_pairing_le (S.hfT z) hg hslab
    refine hmain.trans ?_
    have hterm : ∀ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
        |f z i| * (8 * u) ^ 𝒯.deg i ≤ Cf * (8 ^ 𝒯.deg i) * u ^ (min α η) := by
      intro i hi
      have hi' := (Finset.mem_filter.1 hi).2
      by_cases hfi : f z i = 0
      · rw [hfi, abs_zero, zero_mul]
        have := Real.rpow_nonneg hu.le (min α η)
        have h8 : 0 ≤ (8 : ℝ) ^ 𝒯.deg i := by positivity
        have := S.hCf
        positivity
      · have hαi := S.hα z i hfi
        have h1 := S.hf.1 z hslab hρ i hi'
        have h2 : singularWeight timeZeroDist z ^ min (η - 𝒯.deg i) 0 ≤
            u ^ min (η - 𝒯.deg i) 0 :=
          Real.rpow_le_rpow_of_nonpos hu hw (min_le_right _ _)
        have h3 : |f z i| ≤ Cf * u ^ min (η - 𝒯.deg i) 0 :=
          h1.trans (mul_le_mul_of_nonneg_left h2 S.hCf)
        rw [Real.mul_rpow (by norm_num) hu.le]
        have h4 := rpow_mul_rpow_min hu hu1 (m := min α η) (η := η) (d := 𝒯.deg i)
          ((min_le_left _ _).trans hαi) (min_le_right _ _)
        have h5 : 0 ≤ (8 : ℝ) ^ 𝒯.deg i := by positivity
        calc |f z i| * ((8 : ℝ) ^ 𝒯.deg i * u ^ 𝒯.deg i)
            ≤ (Cf * u ^ min (η - 𝒯.deg i) 0) * ((8 : ℝ) ^ 𝒯.deg i * u ^ 𝒯.deg i) := by
              gcongr
          _ = Cf * (8 ^ 𝒯.deg i) * (u ^ min (η - 𝒯.deg i) 0 * u ^ 𝒯.deg i) := by ring
          _ ≤ Cf * (8 ^ 𝒯.deg i) * u ^ (min α η) :=
              mul_le_mul_of_nonneg_left h4 (mul_nonneg S.hCf h5)
    have hsum : ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ), |f z i| * (8 * u) ^ 𝒯.deg i ≤
        Cf * D8 * u ^ (min α η) := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu.le _)
      refine mul_le_mul_of_nonneg_left ?_ S.hCf
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun i _ _ => by positivity
    have hu5 : (8 * u) ^ 5 = 8 ^ 5 * u ^ (5 : ℝ) := by
      rw [mul_pow, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hpow : u ^ (5 + min α η) = u ^ (5 : ℝ) * u ^ (min α η) := Real.rpow_add hu _ _
    have hc : r4ModelConst 𝒯 γ ≤ |r4ModelConst 𝒯 γ| := le_abs_self _
    have hup5 : 0 ≤ u ^ (5 : ℝ) := Real.rpow_nonneg hu.le _
    calc r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A * (8 * u) ^ 5) *
          ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ), |f z i| * (8 * u) ^ 𝒯.deg i
        ≤ |r4ModelConst 𝒯 γ| * (max 1 CGam * CPi) * (A * (8 * u) ^ 5) *
          (Cf * D8 * u ^ (min α η)) := by
          have h0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
              |f z i| * (8 * u) ^ 𝒯.deg i :=
            Finset.sum_nonneg fun i _ => by positivity
          have h5 : 0 ≤ A * (8 * u) ^ 5 := by positivity
          calc _ ≤ |r4ModelConst 𝒯 γ| * (max 1 CGam * CPi) * (A * (8 * u) ^ 5) *
                ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ), |f z i| * (8 * u) ^ 𝒯.deg i := by
                gcongr
            _ ≤ _ := by gcongr
      _ = _ := by rw [hu5, hpow]; ring

end RegularityStructures

end
