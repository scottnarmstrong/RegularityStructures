/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.SeriesSmall
public import RegularityStructures.Abstract.Ext514W.SettingNear
public import RegularityStructures.Abstract.Ext514W.TermsNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesAllWNear
public import RegularityStructures.Abstract.Singular.KGamma.WrapShellWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Ext514.Bounds
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.Ext514W.SeriesSmall`

The statements of `RegularityStructures.Abstract.Ext514W.SeriesSmall` that involve `Γ`-bounds, for
models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ}

namespace Model

/-- **Small scales** `2^{-n} < d`: `|extU n| ≤ C CΠ max(C_Γ, 1)² d^σ s^{-b}`, `s = 2^n d > 1`. -/
theorem exists_abs_extU_le_of_one_lt_win_near (hh : ShellProfile h N) {γ : ℝ}
    (V : Submodule ℝ (ι → ℝ)) (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (P : PolynomialSector 𝒯 N') {i : ι} (hi : 𝒯.deg i < γ)
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (k : Fin 4 →₀ ℕ) :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ}
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), M.ExtSettingWNear h N γ P I V CPi CGam →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 → 0 < parabolicNorm (y - x) →
      parabolicNorm (y - x) ≤ gammaNearRadius →
      ∀ n : ℕ, 1 < (2 : ℝ) ^ n * parabolicNorm (y - x) →
      |extU M h x y i k n| ≤
        C * (CPi * max CGam 1 * max CGam 1 *
          parabolicNorm (y - x) ^ (𝒯.deg i + 2 - multiDeg k)) *
          ((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ (-b) := by
  classical
  set σ : ℝ := 𝒯.deg i + 2 - multiDeg k with hσdef
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_abs_pairing_shell_le_win_near hh k 𝒯 hdeg4
  choose Cl hCl0 hCl using fun l : Fin 4 →₀ ℕ => exists_abs_pairing_shell_le_win_near hh (k + l) 𝒯 hdeg4
  set Cs : ℝ := C₀ + ∑ l ∈ taylorIdx σ, Cl l with hCs
  have hCsl : ∀ l ∈ taylorIdx σ, Cl l ≤ Cs := fun l hl =>
    (Finset.single_le_sum (f := Cl) (fun l _ => hCl0 l) hl).trans (le_add_of_nonneg_left hC₀0)
  have hCs0 : 0 ≤ Cs := add_nonneg hC₀0 (Finset.sum_nonneg fun l _ => hCl0 l)
  have hC₀s : C₀ ≤ Cs := le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => hCl0 l)
  obtain ⟨b₁, hb₁, hbe₁⟩ := exists_pos_le_finset (extF₁ 𝒯 V k i)
    (fun j => 𝒯.deg j + 2 - multiDeg k) (fun j hj => by
      simp only [extF₁, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      linarith [hj.1])
  obtain ⟨b₂, hb₂, hbe₂⟩ := exists_pos_le_finset (taylorIdx σ) (fun l => σ - multiDeg l)
    (fun l hl => by
      have := (mem_taylorIdx_iff l).1 hl
      linarith)
  refine ⟨min b₁ b₂, ((extF₁ 𝒯 V k i).card + (taylorIdx σ).card) * Cs, lt_min hb₁ hb₂,
    mul_nonneg (by positivity) hCs0, fun M CPi CGam I S x y hx hy hd hxy n hs => ?_⟩
  have hxw := mem_hairerTimeWindow_of_mem_timeSlab (le_refl (1 : ℝ)) hx
  have hyw := mem_hairerTimeWindow_of_mem_timeSlab (le_refl (1 : ℝ)) hy
  have hCw1 : 1 ≤ max CGam 1 := le_max_right _ _
  have hCw0 : 0 ≤ max CGam 1 := zero_le_one.trans hCw1
  have hCPi := S.piBound_nonneg
  have hK : 0 ≤ max 1 CGam * CPi :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi
  have hKe : max 1 CGam * CPi = max CGam 1 * CPi := by rw [max_comm]
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  set d := parabolicNorm (y - x) with hddef
  set s : ℝ := (2 : ℝ) ^ n * d with hsdef
  have hs1 : 1 ≤ s := hs.le
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
  set Y : ℝ := CPi * max CGam 1 * max CGam 1 * d ^ σ with hY
  have hY0 : 0 ≤ Y := by
    have := Real.rpow_nonneg hd.le σ
    rw [hY]; positivity
  have hPy : ∀ j, 𝒯.deg j < γ →
      |derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n| ≤
        Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j) := by
    intro j hj
    have h1 := hC₀ M y n j S.piBound S.piBound_nonneg S.gammaBound S.growth hy.1.le hy.2 hj
    refine h1.trans ?_
    have hZ : 0 ≤ (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j) :=
      mul_nonneg hK (Real.rpow_nonneg hu.le _)
    calc C₀ * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)
        = C₀ * ((max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) := by
          ring
      _ ≤ Cs * ((max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) :=
          mul_le_mul_of_nonneg_right hC₀s hZ
      _ = _ := by ring
  have hPx : ∀ l ∈ taylorIdx σ,
      |derivShellPairing (fun t z => M.regPi x (Pi.single i 1) t z) h (k + l) x n| ≤
        Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - 𝒯.deg i) := by
    intro l hl
    have h1 := hCl l M x n i S.piBound S.piBound_nonneg S.gammaBound S.growth hx.1.le hx.2 hi
    refine h1.trans ?_
    have hZ : 0 ≤ (max 1 CGam * CPi) *
        ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - 𝒯.deg i) :=
      mul_nonneg hK (Real.rpow_nonneg hu.le _)
    calc Cl l * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - 𝒯.deg i)
        = Cl l * ((max 1 CGam * CPi) *
          ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - 𝒯.deg i)) := by ring
      _ ≤ Cs * ((max 1 CGam * CPi) *
          ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - 𝒯.deg i)) :=
          mul_le_mul_of_nonneg_right (hCsl l hl) hZ
      _ = _ := by ring
  refine (S.abs_extU_le_small hi hVi hxw hyw hxy k n hPy hPx).trans ?_
  -- the bound for a term of the first sum
  have hT1 : ∀ j ∈ extF₁ 𝒯 V k i,
      max CGam 1 * d ^ (𝒯.deg i - 𝒯.deg j) *
        (Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) ≤
      Cs * Y * s ^ (-(min b₁ b₂)) := by
    intro j hj
    have hbj := hbe₁ j hj
    have hW : 0 ≤ max CGam 1 * (Cs * (max 1 CGam * CPi)) := mul_nonneg hCw0 (mul_nonneg hCs0 hK)
    have := scale_term_le_of_one_le hd hu hs1 (a := 𝒯.deg i - 𝒯.deg j)
      (p := (multiDeg k : ℝ) - 2 - 𝒯.deg j) (σ := σ) (b := min b₁ b₂)
      (b' := 𝒯.deg j + 2 - multiDeg k) (by rw [hσdef]; ring) (by ring)
      ((min_le_left _ _).trans hbj) _ hW
    calc _ = max CGam 1 * (Cs * (max 1 CGam * CPi)) *
          (d ^ (𝒯.deg i - 𝒯.deg j) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) := by
          ring
      _ ≤ _ := this
      _ = Cs * Y * s ^ (-(min b₁ b₂)) := by rw [hY, hKe, hsdef]; ring
  have hT2 : ∀ l ∈ taylorIdx σ,
      d ^ multiDeg l *
        (Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - 𝒯.deg i)) ≤
      Cs * Y * s ^ (-(min b₁ b₂)) := by
    intro l hl
    have hbl := hbe₂ l hl
    have hW : 0 ≤ Cs * (max 1 CGam * CPi) := mul_nonneg hCs0 hK
    have hadd : ((multiDeg (k + l) : ℕ) : ℝ) = multiDeg k + multiDeg l := by
      have : multiDeg (k + l) = multiDeg k + multiDeg l := map_add _ _ _
      rw [this]; push_cast; ring
    have hdl : d ^ multiDeg l = d ^ ((multiDeg l : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    have := scale_term_le_of_one_le hd hu hs1 (a := ((multiDeg l : ℕ) : ℝ))
      (p := ((multiDeg (k + l) : ℕ) : ℝ) - 2 - 𝒯.deg i) (σ := σ) (b := min b₁ b₂)
      (b' := σ - multiDeg l) (by rw [hadd, hσdef]; ring) (by rw [hadd, hσdef]; ring)
      ((min_le_right _ _).trans hbl) _ hW
    calc _ = Cs * (max 1 CGam * CPi) *
          (d ^ ((multiDeg l : ℕ) : ℝ) *
            ((2 : ℝ) ^ n) ^ (((multiDeg (k + l) : ℕ) : ℝ) - 2 - 𝒯.deg i)) := by
          rw [hdl]; ring
      _ ≤ _ := this
      _ ≤ Cs * Y * s ^ (-(min b₁ b₂)) := by
          have hq : 0 ≤ CPi * max CGam 1 * d ^ σ := by
            have := Real.rpow_nonneg hd.le σ
            positivity
          have hA : 0 ≤ Cs * s ^ (-(min b₁ b₂)) :=
            mul_nonneg hCs0 (Real.rpow_nonneg hs0.le _)
          have h2 := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hq hCw1) hA
          rw [hY, hKe, hsdef] at *
          calc _ = (Cs * ((2 : ℝ) ^ n * d) ^ (-(min b₁ b₂))) * (CPi * max CGam 1 * d ^ σ) := by
                ring
            _ ≤ (Cs * ((2 : ℝ) ^ n * d) ^ (-(min b₁ b₂))) *
                (CPi * max CGam 1 * d ^ σ * max CGam 1) := h2
            _ = _ := by ring
  have hsum := add_le_add (Finset.sum_le_card_nsmul _ _ _ hT1)
    (Finset.sum_le_card_nsmul _ _ _ hT2)
  refine hsum.trans (le_of_eq ?_)
  simp only [nsmul_eq_mul]
  ring

end Model

end RegularityStructures

end
