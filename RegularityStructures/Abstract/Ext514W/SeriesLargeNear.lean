/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.IdentityNear
public import RegularityStructures.Abstract.Ext514W.SeriesSmallNear
public import RegularityStructures.Abstract.Ext514W.SettingNear
public import RegularityStructures.Abstract.Ext514W.TermsNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesAllWNear
public import RegularityStructures.Abstract.Singular.KGamma.WrapShellWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Ext514.Bounds
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.PolyPairing
public import RegularityStructures.Abstract.Profile.Realising

/-!
# The series for the polynomial components of `Γ_{yx} I e_i`: large scales, near-pair `Γ`-bounds

For `s = 2^n d ≤ 1` the term `extU n` of the series is estimated through its large-scale form, with
the Taylor kernel for an exponent `σ' > σ`: `exists_abs_extU_le_of_le_one_win_near` gives
`|extU n| ≤ C CΠ max(C_Γ, 1)² d^σ s^a` with `a > 0`.

The statements are in the window extension setting `ExtSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ}

namespace Model

/-- **Large scales** `2^{-n} ≥ d`: `|extU n| ≤ C CΠ max(C_Γ, 1)² d^σ s^a`, `s = 2^n d ≤ 1`. -/
theorem exists_abs_extU_le_of_le_one_win_near (hh : ShellProfile h N) {γ : ℝ}
    (V : Submodule ℝ (ι → ℝ)) (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (P : PolynomialSector 𝒯 N') {i : ι} (hi : 𝒯.deg i < γ)
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (k : Fin 4 →₀ ℕ)
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2)
    (hnat1 : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ 𝒯.deg i + 2 - multiDeg k)
    (hnat2 : ∀ j, j ∉ Set.range P.emb → (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j ≤ 𝒯.deg i →
      (multiDeg k : ℝ) ≠ 𝒯.deg j + 2) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ}
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), M.ExtSettingWNear h N γ P I V CPi CGam →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 → 0 < parabolicNorm (y - x) →
      ∀ n : ℕ, (2 : ℝ) ^ n * parabolicNorm (y - x) ≤ 1 →
      |extU M h x y i k n| ≤
        C * (CPi * max CGam 1 * max CGam 1 *
          parabolicNorm (y - x) ^ (𝒯.deg i + 2 - multiDeg k)) *
          ((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ a := by
  classical
  set σ : ℝ := 𝒯.deg i + 2 - multiDeg k with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  set σ' : ℝ := (⌈σ⌉ : ℝ) with hσ'def
  have hlt : σ < σ' := lt_ceil_of_forall_multiDeg_ne hσ hnat1
  have hσ' : 0 < σ' := hσ.trans hlt
  obtain ⟨C₁, hC₁0, H₁⟩ := exists_abs_pairing_dTaylor_all_le_win_near hh k hσ' 𝒯 hdeg4
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_abs_pairing_shell_le_win_near hh k 𝒯 hdeg4
  set Sx : Finset ι := Finset.univ.image P.emb with hSx
  obtain ⟨a₁, ha₁, hae₁⟩ := exists_pos_le_finset (extF₂ 𝒯 V k i Sx)
    (fun j => (multiDeg k : ℝ) - 𝒯.deg j - 2) (fun j hj => by
      simp only [extF₂, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨hnk, hVj, hji, hjS⟩ := hj
      have hjr : j ∉ Set.range P.emb := fun hr => hjS (by
        obtain ⟨l, hl⟩ := hr
        exact Finset.mem_image.2 ⟨l, Finset.mem_univ _, hl⟩)
      have hne := hnat2 j hjr hVj hji
      rcases lt_or_gt_of_ne hne with h1 | h1
      · exact absurd h1 hnk
      · linarith)
  refine ⟨min a₁ (σ' - σ), C₁ + (extF₂ 𝒯 V k i Sx).card * C₀,
    lt_min ha₁ (by linarith), by positivity, fun M CPi CGam I S x y hx hy hd n hs => ?_⟩
  have hxy : parabolicNorm (y - x) ≤ gammaNearRadius := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have := parabolicNorm_nonneg (y - x)
    have h2 : parabolicNorm (y - x) ≤ (2 : ℝ) ^ n * parabolicNorm (y - x) := by nlinarith
    exact le_gammaNearRadius_of_le_one (h2.trans hs)
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
  have hs0 : 0 < s := by rw [hsdef]; positivity
  set a : ℝ := min a₁ (σ' - σ) with hadef
  set Y : ℝ := CPi * max CGam 1 * max CGam 1 * d ^ σ with hY
  have hdσ : 0 ≤ d ^ σ := Real.rpow_nonneg hd.le σ
  have hdn : d ≤ ((2 : ℝ) ^ n)⁻¹ := by
    calc d = s * ((2 : ℝ) ^ n)⁻¹ := by rw [hsdef]; field_simp
      _ ≤ 1 * ((2 : ℝ) ^ n)⁻¹ := mul_le_mul_of_nonneg_right hs (inv_nonneg.2 hu.le)
      _ = _ := one_mul _
  have hKd : max 1 CGam * CPi * d ^ σ ≤ Y := by
    rw [hKe, hY]
    have hq : 0 ≤ CPi * max CGam 1 * d ^ σ := by positivity
    calc max CGam 1 * CPi * d ^ σ = CPi * max CGam 1 * d ^ σ := by ring
      _ ≤ (CPi * max CGam 1 * d ^ σ) * max CGam 1 := le_mul_of_one_le_right hq hCw1
      _ = _ := by ring
  have hlarge := S.extU_eq_large hi hVi x y k n
  rw [← hσdef] at hlarge
  rw [← dTaylorKernel_ceil h k n σ x y] at hlarge
  rw [hlarge]
  refine (abs_sub _ _).trans ?_
  -- the pairing
  have hP := H₁ M n i S.piBound S.piBound_nonneg S.gammaBound S.growth hx.1.le hx.2 hy.1.le hy.2
    hi hd hdn
  have hP' : |parabolicSemigroup.pairing (fun t z => M.regPi x (Pi.single i 1) t z)
      (dTaylorKernel h k n σ' x y)| ≤ C₁ * Y * s ^ a := by
    refine hP.trans ?_
    have := scale_term_le_of_le_one hd hu hs (a := σ')
      (p := σ' + multiDeg k - 2 - 𝒯.deg i) (σ := σ) (c := a) (c' := σ' - σ)
      (by rw [hσdef]; ring) (by rw [hσdef]; ring) (min_le_right _ _) (C₁ * (max 1 CGam * CPi))
      (mul_nonneg hC₁0 hK)
    calc _ = C₁ * (max 1 CGam * CPi) *
          (d ^ σ' * ((2 : ℝ) ^ n) ^ (σ' + multiDeg k - 2 - 𝒯.deg i)) := by ring
      _ ≤ _ := this
      _ = (C₁ * s ^ a) * (max 1 CGam * CPi * d ^ σ) := by rw [hsdef]; ring
      _ ≤ (C₁ * s ^ a) * Y := mul_le_mul_of_nonneg_left hKd
          (mul_nonneg hC₁0 (Real.rpow_nonneg hs0.le _))
      _ = _ := by ring
  -- the remainder
  have hS0 : ∀ j ∈ Sx, ∀ (y : ParabolicSpace) (n : ℕ),
      derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n = 0 := by
    intro j hj y n
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hj
    exact Model.derivShellPairing_regPi_emb_eq_zeroP S.realising.poly hh S.poly_le y ⟨l, rfl⟩ k n
  have hPy : ∀ j, 𝒯.deg j < γ →
      |derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n| ≤
        C₀ * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j) :=
    fun j hj => hC₀ M y n j S.piBound S.piBound_nonneg S.gammaBound S.growth hy.1.le hy.2 hj
  have hR := S.abs_extR_le hi hVi hxw hyw hxy k n Sx hS0 hPy
  have hT : ∀ j ∈ extF₂ 𝒯 V k i Sx,
      max CGam 1 * d ^ (𝒯.deg i - 𝒯.deg j) *
        (C₀ * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) ≤
      C₀ * Y * s ^ a := by
    intro j hj
    have haj := hae₁ j hj
    have hW : 0 ≤ max CGam 1 * (C₀ * (max 1 CGam * CPi)) := by positivity
    have := scale_term_le_of_le_one hd hu hs (a := 𝒯.deg i - 𝒯.deg j)
      (p := (multiDeg k : ℝ) - 2 - 𝒯.deg j) (σ := σ) (c := a)
      (c' := (multiDeg k : ℝ) - 2 - 𝒯.deg j) (by rw [hσdef]; ring) rfl
      (by linarith [haj, min_le_left a₁ (σ' - σ)]) _ hW
    calc _ = max CGam 1 * (C₀ * (max 1 CGam * CPi)) *
          (d ^ (𝒯.deg i - 𝒯.deg j) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) := by
          ring
      _ ≤ max CGam 1 * (C₀ * (max 1 CGam * CPi)) * (d ^ σ * s ^ a) := this
      _ = C₀ * Y * s ^ a := by rw [hY, hKe]; ring
  have hRs := hR.trans (Finset.sum_le_card_nsmul _ _ _ hT)
  rw [nsmul_eq_mul] at hRs
  refine (add_le_add hP' hRs).trans (le_of_eq ?_)
  ring

end Model

end RegularityStructures

end
