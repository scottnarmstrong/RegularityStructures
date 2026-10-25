/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesAllWNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesLargeWNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesTauWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.SeriesAux
public import RegularityStructures.Abstract.Singular.KGamma.SeriesBig
public import RegularityStructures.Abstract.Singular.KGamma.SeriesLinearW
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# Large-scale Taylor-kernel bounds, near-pair `Γ`-bounds

At the large scales `2^n W ≤ 128`, both `⟨Π_x f(x), K^{k,σ}_{n;yx}⟩` and `⟨R f, K^{k,σ}_{n;yx}⟩` are
bounded by `C K₀ C_f d^σ (2^n)^{σ+|k|−2−γ} W^{α∧η−γ}`, for models whose `Γ`-bounds hold only for
near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N N' : ℕ}
  {h : ParabolicSpace → ℝ}

/-- `⟨Π_x f(x), K^{k,σ'}_{n;yx}⟩` for `2^n W ≤ 128`:
`≤ C K₀ C_f d^{σ'} (2^n)^{σ'+|k|−2−γ} W^{α∧η−γ}`. -/
theorem exists_abs_pairing_fx_dTaylor_le_win_near (hh : ShellProfile h N) (k : Fin 4 →₀ ℕ) {σ : ℝ}
    (hσ : 0 < σ) (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {x y : ParabolicSpace}, SlabPair T x y → ∀ n : ℕ,
      parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ →
      (2 : ℝ) ^ n * min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ≤ 128 →
      |parabolicSemigroup.pairing (M.regPi x (f x)) (dTaylorKernel h k n σ x y)| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
          ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - γ)) *
            min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ) := by
  classical
  obtain ⟨Cp, hCp0, hCp⟩ := Model.exists_abs_pairing_dTaylor_all_le_win_near hh k hσ 𝒯 hdeg
  set c128 : ℝ := ∑ j : ι, (128 : ℝ) ^ |γ - 𝒯.deg j| with hc128
  have hc0 : 0 ≤ c128 := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨Fintype.card ι * Cp * c128, by positivity,
    fun M f T Cf CPi CGam S x y Pr n hdn h128 => ?_⟩
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hd := Pr.hd
  have hW := Pr.W_pos
  have hW1 := Pr.W_le_one
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  set W := min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with hWdef
  set q : ℝ := σ + multiDeg k - 2 - γ with hq
  set Cterm : ℝ := Cp * c128 * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
    ((2 : ℝ) ^ n) ^ q) * W ^ (min α η - γ) with hCterm
  have hCterm0 : 0 ≤ Cterm := by
    have := S.hCf
    rw [hCterm]; positivity
  rw [M.pairing_regPi_dTaylor_eq_sum_win hh k hσ S.hgrowth S.hdeg (S.hfT x) n hd hdn]
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), |f x i * parabolicSemigroup.pairing
      (M.regPi x (Pi.single i 1)) (dTaylorKernel h k n σ x y)| ≤ Cterm := by
    intro i _
    by_cases hfi : f x i = 0
    · rw [hfi, zero_mul, abs_zero]; exact hCterm0
    · have hi : 𝒯.deg i < γ := by
        by_contra hge
        exact hfi ((mem_lowerSubspace).1 (S.hfT x) i (not_lt.1 hge))
      have hαi : α ≤ 𝒯.deg i := S.hα x i hfi
      have hf1 := S.hf.1 x Pr.hx (timeZeroDist_pos_of_mem_timeSlab Pr.hx) i hi
      have hP := hCp M n i S.hPi S.hCPi S.hGam S.hgrowth Pr.hx.1.le (S.fst_le_one_of_mem_timeSlab Pr.hx)
        Pr.hy.1.le (S.fst_le_one_of_mem_timeSlab Pr.hy) hi hd hdn
      set m : ℝ := min (η - 𝒯.deg i) 0 with hm
      have hm0 : m ≤ 0 := min_le_right _ _
      have hwx : singularWeight timeZeroDist x ^ m ≤ W ^ m :=
        Real.rpow_le_rpow_of_nonpos hW Pr.W_le_x hm0
      have hexp : σ + multiDeg k - 2 - 𝒯.deg i = q + (γ - 𝒯.deg i) := by rw [hq]; ring
      rw [hexp, Real.rpow_add hu] at hP
      have hu1 := rpow_le_of_mul_le hu hW h128 (sub_nonneg.2 hi.le)
      have hc1 : (128 : ℝ) ^ (γ - 𝒯.deg i) ≤ c128 :=
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self _)).trans
          (Finset.single_le_sum (f := fun j : ι => (128 : ℝ) ^ |γ - 𝒯.deg j|)
            (fun j _ => by positivity) (Finset.mem_univ i))
      have hWe : W ^ m * W ^ (-(γ - 𝒯.deg i)) ≤ W ^ (min α η - γ) := by
        rw [← Real.rpow_add hW]
        refine Real.rpow_le_rpow_of_exponent_ge hW hW1 ?_
        have h1 : min α η ≤ η := min_le_right _ _
        have h2 : min α η ≤ 𝒯.deg i := (min_le_left _ _).trans hαi
        rcases le_total (η - 𝒯.deg i) 0 with h | h
        · rw [hm, min_eq_left h]; linarith
        · rw [hm, min_eq_right h]; linarith
      set g : ℝ := γ - 𝒯.deg i with hg
      have hZ : 0 ≤ Cp * (max 1 CGam * CPi) * (parabolicNorm (y - x) ^ σ * ((2 : ℝ) ^ n) ^ q) := by
        positivity
      have hWm : 0 ≤ W ^ m := Real.rpow_nonneg hW.le _
      have hWg : 0 ≤ W ^ (-g) := Real.rpow_nonneg hW.le _
      have hug : ((2 : ℝ) ^ n) ^ g ≤ c128 * W ^ (-g) :=
        hu1.trans (mul_le_mul_of_nonneg_right hc1 hWg)
      have hCf := S.hCf
      rw [abs_mul]
      calc |f x i| * |parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
            (dTaylorKernel h k n σ x y)|
          ≤ (Cf * singularWeight timeZeroDist x ^ m) * (Cp * (max 1 CGam * CPi) *
            (parabolicNorm (y - x) ^ σ * (((2 : ℝ) ^ n) ^ q * ((2 : ℝ) ^ n) ^ g))) :=
            mul_le_mul hf1 hP (abs_nonneg _)
              (mul_nonneg hCf (Real.rpow_nonneg Pr.weight_x_pos.le _))
        _ = (Cf * singularWeight timeZeroDist x ^ m) * ((Cp * (max 1 CGam * CPi) *
            (parabolicNorm (y - x) ^ σ * ((2 : ℝ) ^ n) ^ q)) * ((2 : ℝ) ^ n) ^ g) := by ring
        _ ≤ (Cf * W ^ m) * ((Cp * (max 1 CGam * CPi) *
            (parabolicNorm (y - x) ^ σ * ((2 : ℝ) ^ n) ^ q)) * (c128 * W ^ (-g))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hwx hCf) ?_ (by positivity)
              (by positivity)
            exact mul_le_mul_of_nonneg_left hug hZ
        _ = (Cp * c128 * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
            ((2 : ℝ) ^ n) ^ q)) * (W ^ m * W ^ (-g)) := by ring
        _ ≤ (Cp * c128 * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
            ((2 : ℝ) ^ n) ^ q)) * W ^ (min α η - γ) :=
            mul_le_mul_of_nonneg_left hWe (by positivity)
        _ = Cterm := by rw [hCterm]
  calc _ ≤ ∑ i, |f x i * parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
        (dTaylorKernel h k n σ x y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, Cterm := Finset.sum_le_sum hterm
    _ = Fintype.card ι * Cterm := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by rw [hCterm]; ring

/-- `⟨R f, K^{k,σ}_{n;yx}⟩` for `2^n W ≤ 128`:
`≤ C K₀ C_f d^{σ} (2^n)^{σ+|k|−2−γ} W^{α∧η−γ}`. -/
theorem exists_abs_latticeRecon_dTaylor_big_le_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ) {σ : ℝ} (hσ : 0 < σ)
    (𝒯 : RegularityStructure ι) (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hγ : 0 < γ) (hαγ : α ≤ γ) (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {x y : ParabolicSpace}, SlabPair T x y → ∀ n : ℕ,
      parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ →
      (2 : ℝ) ^ n * min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ≤ 128 →
      |M.latticeRecon f (dTaylorKernel h k n σ x y)| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
          ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - γ)) *
            min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ) := by
  obtain ⟨Cc, hCc0, hCc⟩ := Model.exists_abs_latticeRecon_dTaylor_all_le_win_near hh hc k hσ 𝒯 γ η α hdeg
    hγ hαγ hαη
  refine ⟨Cc * 128 ^ (γ - min α η), by positivity,
    fun M f T Cf CPi CGam S x y Pr n hdn h128 => ?_⟩
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hd := Pr.hd
  have hW := Pr.W_pos
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hb := hCc M f T Cf CPi CGam S n Pr.hx.2 Pr.hy.2 hd hdn
  have hγβ : 0 ≤ γ - min α η := by linarith [min_le_left α η, S.hαγ]
  have hu1 := rpow_le_of_mul_le hu hW h128 hγβ
  have hexp : σ + multiDeg k - 2 - min α η =
      (σ + multiDeg k - 2 - γ) + (γ - min α η) := by ring
  rw [hexp, Real.rpow_add hu] at hb
  have hneg : -(γ - min α η) = min α η - γ := by ring
  rw [hneg] at hu1
  have hCf := S.hCf
  refine hb.trans ?_
  have hX : 0 ≤ Cc * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
      ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - γ)) := by positivity
  calc _ ≤ Cc * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
        ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - γ)) * (128 ^ (γ - min α η) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ)) := by
        have := mul_le_mul_of_nonneg_left hu1 hX
        calc _ = Cc * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
            ((2 : ℝ) ^ n) ^ (σ + multiDeg k - 2 - γ)) * ((2 : ℝ) ^ n) ^ (γ - min α η) := by ring
          _ ≤ _ := this
    _ = _ := by ring

end RegularityStructures

end
