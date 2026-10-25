/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.SeriesLargeNear
public import RegularityStructures.Abstract.Ext514W.SeriesSmallNear
public import RegularityStructures.Abstract.Ext514W.SettingNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Ext514.Bracket
public import RegularityStructures.Abstract.Singular.KGamma.Geom

/-!
# Bound on the polynomial series of `Γ_{yx} I e_i`, near-pair `Γ`-bounds

Under `ExtSettingWNear`, for `x, y ∈ timeSlab 1` with `0 < d(y, x) ≤ gammaNearRadius`, the series
`∑ₙ extU n` converges and is bounded by `c C_Π max(C_Γ, 1)² d(y, x)^{deg i + 2 − |k|}`, for models
whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ}

namespace Model

theorem exists_abs_tsum_extU_le_win_near (hh : ShellProfile h N) {γ : ℝ} (V : Submodule ℝ (ι → ℝ))
    (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (P : PolynomialSector 𝒯 N') {i : ι} (hi : 𝒯.deg i < γ)
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (k : Fin 4 →₀ ℕ)
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2)
    (hnat1 : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ 𝒯.deg i + 2 - multiDeg k)
    (hnat2 : ∀ j, j ∉ Set.range P.emb → (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j ≤ 𝒯.deg i →
      (multiDeg k : ℝ) ≠ 𝒯.deg j + 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ}
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), M.ExtSettingWNear h N γ P I V CPi CGam →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 → 0 < parabolicNorm (y - x) →
      parabolicNorm (y - x) ≤ gammaNearRadius →
      Summable (extU M h x y i k) ∧
      |∑' n, extU M h x y i k n| ≤
        c * CPi * max CGam 1 * max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i + 2 - multiDeg k) := by
  obtain ⟨b, Cs, hb, hCs0, Hs⟩ := exists_abs_extU_le_of_one_lt_win_near hh V hdeg4 P hi hVi k
  obtain ⟨a, Cl, ha, hCl0, Hl⟩ := exists_abs_extU_le_of_le_one_win_near hh V hdeg4 P hi hVi k hk hnat1
    hnat2
  obtain ⟨Cg, hCg0, hCg⟩ := KGammaSup.exists_summable_abs_tsum_le a b ha hb
  refine ⟨Cg * max Cs Cl, mul_nonneg hCg0 (hCs0.trans (le_max_left _ _)),
    fun M CPi CGam I S x y hx hy hd hxy => ?_⟩
  have hCw1 : 1 ≤ max CGam 1 := le_max_right _ _
  have hCw0 : 0 ≤ max CGam 1 := zero_le_one.trans hCw1
  have hCPi := S.piBound_nonneg
  set d := parabolicNorm (y - x) with hddef
  set σ : ℝ := 𝒯.deg i + 2 - multiDeg k with hσdef
  have hdσ : 0 ≤ d ^ σ := Real.rpow_nonneg hd.le σ
  set Y : ℝ := CPi * max CGam 1 * max CGam 1 * d ^ σ with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hmax0 : 0 ≤ max Cs Cl := hCs0.trans (le_max_left _ _)
  have hbound : ∀ n : ℕ, |extU M h x y i k n| ≤
      (max Cs Cl * Y) * min (((2 : ℝ) ^ n * d) ^ a) (((2 : ℝ) ^ n * d) ^ (-b)) := by
    intro n
    have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    set s : ℝ := (2 : ℝ) ^ n * d with hsdef
    have hs0 : 0 < s := by rw [hsdef]; positivity
    rcases le_or_gt s 1 with hs1 | hs1
    · have := Hl M I S hx hy hd n hs1
      have hmin : min (s ^ a) (s ^ (-b)) = s ^ a := by
        refine min_eq_left ?_
        calc s ^ a ≤ 1 := Real.rpow_le_one hs0.le hs1 ha.le
          _ ≤ s ^ (-b) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 (by linarith)
      rw [hmin]
      refine this.trans ?_
      have h2 : 0 ≤ Y * s ^ a := mul_nonneg hY0 (Real.rpow_nonneg hs0.le _)
      calc Cl * Y * s ^ a = Cl * (Y * s ^ a) := by ring
        _ ≤ max Cs Cl * (Y * s ^ a) := mul_le_mul_of_nonneg_right (le_max_right _ _) h2
        _ = _ := by ring
    · have := Hs M I S hx hy hd hxy n hs1
      have hmin : min (s ^ a) (s ^ (-b)) = s ^ (-b) := by
        refine min_eq_right ?_
        calc s ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1.le (by linarith)
          _ ≤ s ^ a := Real.one_le_rpow hs1.le ha.le
      rw [hmin]
      refine this.trans ?_
      have h2 : 0 ≤ Y * s ^ (-b) := mul_nonneg hY0 (Real.rpow_nonneg hs0.le _)
      calc Cs * Y * s ^ (-b) = Cs * (Y * s ^ (-b)) := by ring
        _ ≤ max Cs Cl * (Y * s ^ (-b)) := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
        _ = _ := by ring
  obtain ⟨hs, hb'⟩ := hCg d hd (extU M h x y i k) (max Cs Cl * Y) (mul_nonneg hmax0 hY0) hbound
  refine ⟨hs, ?_⟩
  have h1 : |∑' n, extU M h x y i k n| ≤ ∑' n, |extU M h x y i k n| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  refine h1.trans (hb'.trans (le_of_eq ?_))
  rw [hY]; ring

end Model

end RegularityStructures

end
