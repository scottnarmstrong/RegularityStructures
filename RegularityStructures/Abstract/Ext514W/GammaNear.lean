/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.IdentityNear
public import RegularityStructures.Abstract.Ext514W.PolyBoundNear
public import RegularityStructures.Abstract.Ext514W.SettingNear
public import RegularityStructures.Abstract.Singular.Window.BasicNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Ext514.Bracket
public import RegularityStructures.Abstract.Integration.SchauderPoly

/-!
# The bound for `Γ` on the integrated symbols `I e_i`, near-pair `Γ`-bounds

[Hai14, Theorem 5.14, (5.18)] in window form: for a model realising the kernel with profile `h` for
`I` on the sector `V`, `e_i ∈ V`, `deg i < γ`, `x, y` in the time slab `(0, 1]` with
`d(y, x) ≤ gammaNearRadius`, and `deg j < deg i + 2`,
`|(Γ_{yx} I e_i)_j| ≤ c (C_I + C_Π max(C_Γ, 1)) max(C_Γ, 1) d(y, x)^{deg i + 2 − deg j}`
(`exists_abs_gammaMap_integral_le_win_near`). The constant `c` is independent of the model. The
non-polynomial components are bounded separately
(`ExtSettingWNear.abs_gammaMap_integral_nonpoly_le`).

The statements are in the window extension setting `ExtSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam CI : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

/-- The non-polynomial components of `Γ_{yx} I e_i`, window version:
`|(Γ_{yx} I e_i)_j| ≤ card ι C_I max(C_Γ, 1) d^{deg i + 2 − deg j}` for `j ∉ T̄`,
`deg j < deg i + 2`, `x, y` in the window. -/
theorem ExtSettingWNear.abs_gammaMap_integral_nonpoly_le (S : ExtSettingWNear M h N γ P I V CPi CGam)
    (hCI : ∀ a b, |I (Pi.single a 1) b| ≤ CI) {i : ι} (hi : 𝒯.deg i < γ)
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) {x y : ParabolicSpace} (hx : x ∈ hairerTimeWindow)
    (hy : y ∈ hairerTimeWindow) (hxy : parabolicNorm (y - x) ≤ gammaNearRadius) {j : ι}
    (hj : j ∉ Set.range P.emb)
    (hjlt : 𝒯.deg j < 𝒯.deg i + 2) :
    |M.gammaMap y x (I (Pi.single i 1)) j| ≤ Fintype.card ι * (CI * max CGam 1 *
      parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j)) := by
  have hcomm := S.integration.comm _ (M.gamma y x).2 _ hVi
  have hE : M.gammaMap y x (I (Pi.single i 1)) j = I (M.gammaMap y x (Pi.single i 1)) j := by
    have := hcomm j hj
    simp only [Pi.sub_apply] at this
    change I (M.gammaMap y x (Pi.single i 1)) j - M.gammaMap y x (I (Pi.single i 1)) j = 0 at this
    linarith
  have hsum : I (M.gammaMap y x (Pi.single i 1)) j =
      ∑ j', M.gammaMap y x (Pi.single i 1) j' * I (Pi.single j' 1) j := by
    conv_lhs => rw [eq_sum_single (M.gammaMap y x (Pi.single i 1))]
    simp [map_sum, Finset.sum_apply]
  rw [hE, hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI i j)
  have hmax : 0 ≤ max CGam 1 := le_trans zero_le_one (le_max_right _ _)
  have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  calc ∑ j', |M.gammaMap y x (Pi.single i 1) j' * I (Pi.single j' 1) j|
      ≤ ∑ _j' : ι, (CI * max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j)) := by
        refine Finset.sum_le_sum fun j' _ => ?_
        rw [abs_mul]
        by_cases hτ : M.gammaMap y x (Pi.single i 1) j' = 0
        · simp only [hτ, abs_zero, zero_mul]
          positivity
        · by_cases hI0 : I (Pi.single j' 1) j = 0
          · simp only [hI0, abs_zero, mul_zero]
            positivity
          · obtain ⟨hVj, -, hji⟩ := S.gammaMap_single_support hi hVi x y hτ
            have hhom := S.integration.map_homogeneous (𝒯.deg j') (Pi.single j' 1) hVj
              (single_mem_homogeneousSubspace j' 1)
            have hdj : 𝒯.deg j = 𝒯.deg j' + 2 := by
              by_contra hne
              exact hI0 ((mem_homogeneousSubspace.1 hhom) j (by
                intro h'; apply hne; linarith))
            have hjj : j' ≠ i := by
              rintro rfl
              linarith
            have hlt : 𝒯.deg j' < 𝒯.deg i := by
              refine lt_of_le_of_ne hji fun h' => hτ ?_
              exact (M.isGradedUnipotent_gammaMap y x).apply_single_of_le hjj h'.symm.le
            have h1 := M.abs_gammaMap_single_le_of_window_near S.gammaBound hi hlt hx hy hxy
            have hexp : 𝒯.deg i - 𝒯.deg j' = 𝒯.deg i + 2 - 𝒯.deg j := by rw [hdj]; ring
            rw [hexp] at h1
            have h2 := hCI j' j
            calc |M.gammaMap y x (Pi.single i 1) j'| * |I (Pi.single j' 1) j|
                ≤ (CGam * parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j)) * CI :=
                  mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
              _ ≤ (max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j)) * CI :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
                    (Real.rpow_nonneg hd0 _)) hCI0
              _ = _ := by ring
    _ = _ := by simp

/-- **The bound for `Γ` on `I e_i`, window version** [Hai14, Theorem 5.14, (5.18)]: there is a
constant `c` (depending on `𝒯, V, γ, h, P, i`, not on the model) such that for `x, y` in the time
slab `(0, 1]` and `deg j < deg i + 2`,
`|(Γ_{yx} I e_i)_j| ≤ c (C_I + C_Π max(C_Γ, 1)) max(C_Γ, 1) d(y, x)^{deg i + 2 − deg j}`. -/
theorem exists_abs_gammaMap_integral_le_win_near (hh : ShellProfile h N) {γ : ℝ}
    (V : Submodule ℝ (ι → ℝ)) (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (P : PolynomialSector 𝒯 N') {i : ι} (hi : 𝒯.deg i < γ)
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V)
    (hnat1 : ∀ k : PolyIndex N', polyDeg N' k < 𝒯.deg i + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ 𝒯.deg i + 2 - multiDeg k.1)
    (hnat2 : ∀ k : PolyIndex N', polyDeg N' k < 𝒯.deg i + 2 →
      ∀ j, j ∉ Set.range P.emb → (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j ≤ 𝒯.deg i →
        (multiDeg k.1 : ℝ) ≠ 𝒯.deg j + 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam CI : ℝ}
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), M.ExtSettingWNear h N γ P I V CPi CGam →
      (∀ a b, |I (Pi.single a 1) b| ≤ CI) → ∀ {x y : ParabolicSpace},
      x ∈ timeSlab 1 → y ∈ timeSlab 1 → parabolicNorm (y - x) ≤ gammaNearRadius →
      ∀ (j : ι), 𝒯.deg j < 𝒯.deg i + 2 →
      |M.gammaMap y x (I (Pi.single i 1)) j| ≤
        c * (CI + CPi * max CGam 1) * max CGam 1 *
          parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j) := by
  classical
  have hk : ∀ k : PolyIndex N', ∃ c : ℝ, 0 ≤ c ∧ (polyDeg N' k < 𝒯.deg i + 2 →
      ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ} (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)),
      M.ExtSettingWNear h N γ P I V CPi CGam → ∀ {x y : ParabolicSpace},
      x ∈ timeSlab 1 → y ∈ timeSlab 1 → 0 < parabolicNorm (y - x) →
      parabolicNorm (y - x) ≤ gammaNearRadius →
      Summable (extU M h x y i k.1) → |∑' n, extU M h x y i k.1 n| ≤
        c * CPi * max CGam 1 * max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i + 2 - multiDeg k.1)) := by
    intro k
    by_cases hlt : polyDeg N' k < 𝒯.deg i + 2
    · obtain ⟨c, hc0, hc⟩ := exists_abs_tsum_extU_le_win_near hh V hdeg4 P hi hVi k.1 hlt (hnat1 k hlt)
        (hnat2 k hlt)
      exact ⟨c, hc0, fun _ M CPi CGam I S x y hx hy hd hxy' _ => (hc M I S hx hy hd hxy').2⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hlt⟩
  choose ck hck0 hck using hk
  refine ⟨∑ k, ck k + Fintype.card ι, add_nonneg (Finset.sum_nonneg fun k _ => hck0 k)
    (Nat.cast_nonneg _), ?_⟩
  intro M CPi CGam CI I S hCI x y hx hy hxy j hjlt
  have hxw := mem_hairerTimeWindow_of_mem_timeSlab (le_refl (1 : ℝ)) hx
  have hyw := mem_hairerTimeWindow_of_mem_timeSlab (le_refl (1 : ℝ)) hy
  have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI i j)
  have hCPi := S.piBound_nonneg
  have hmax1 : 1 ≤ max CGam 1 := le_max_right _ _
  have hmax : 0 ≤ max CGam 1 := zero_le_one.trans hmax1
  have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  have hpow : 0 ≤ parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j) := Real.rpow_nonneg hd0 _
  have hRHS0 : 0 ≤ (CI + CPi * max CGam 1) * max CGam 1 *
      parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j) :=
    mul_nonneg (mul_nonneg (add_nonneg hCI0 (mul_nonneg hCPi hmax)) hmax) hpow
  by_cases hj : j ∈ Set.range P.emb
  · obtain ⟨k, rfl⟩ := hj
    have hdk : 𝒯.deg (P.emb k) = polyDeg N' k := P.deg_emb k
    have hlt : polyDeg N' k < 𝒯.deg i + 2 := by rw [← hdk]; exact hjlt
    have hkf : (1 : ℝ) ≤ multiFactorial k.1 := by exact_mod_cast multiFactorial_pos k.1
    have hσ : 0 < 𝒯.deg i + 2 - (multiDeg k.1 : ℝ) := by
      have : (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 := hlt
      linarith
    have hexp : 𝒯.deg i + 2 - 𝒯.deg (P.emb k) = 𝒯.deg i + 2 - (multiDeg k.1 : ℝ) := by
      rw [hdk]; rfl
    rw [hexp]
    have hcc : 0 ≤ ∑ k, ck k + (Fintype.card ι : ℝ) :=
      add_nonneg (Finset.sum_nonneg fun k _ => hck0 k) (Nat.cast_nonneg _)
    by_cases hd : parabolicNorm (y - x) = 0
    · have hyx : y = x := sub_eq_zero.1 (eq_zero_of_parabolicNorm_eq_zero hd)
      subst hyx
      rw [M.gammaMap_self]
      simp only [LinearMap.id_apply]
      rw [S.integration_poly _ hVi k, abs_zero]
      positivity
    · have hdpos : 0 < parabolicNorm (y - x) := lt_of_le_of_ne hd0 (Ne.symm hd)
      obtain ⟨hsum, hbr⟩ := S.poly_bracket_ext hi hVi x y k hlt
      have h1 := hck k hlt M I S hx hy hdpos hxy hsum
      rw [← hbr, abs_mul, abs_of_pos (lt_of_lt_of_le one_pos hkf)] at h1
      have h2 : |M.gammaMap y x (I (Pi.single i 1)) (P.emb k)| ≤
          |M.gammaMap y x (I (Pi.single i 1)) (P.emb k)| * multiFactorial k.1 :=
        le_mul_of_one_le_right (abs_nonneg _) hkf
      refine h2.trans (h1.trans ?_)
      have hck1 : ck k ≤ ∑ k, ck k + (Fintype.card ι : ℝ) :=
        (Finset.single_le_sum (fun k _ => hck0 k) (Finset.mem_univ k)).trans
          (le_add_of_nonneg_right (Nat.cast_nonneg _))
      have h3 : ck k * CPi * max CGam 1 * max CGam 1 ≤
          (∑ k, ck k + (Fintype.card ι : ℝ)) * (CI + CPi * max CGam 1) * max CGam 1 := by
        have h4 : ck k * (CPi * max CGam 1) ≤
            (∑ k, ck k + (Fintype.card ι : ℝ)) * (CI + CPi * max CGam 1) :=
          mul_le_mul hck1 (by linarith) (mul_nonneg hCPi hmax) hcc
        calc ck k * CPi * max CGam 1 * max CGam 1 = ck k * (CPi * max CGam 1) * max CGam 1 := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h4 hmax
      exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hd0 _)
  · have hnp := S.abs_gammaMap_integral_nonpoly_le hCI hi hVi hxw hyw hxy hj hjlt
    refine hnp.trans ?_
    have hcard : (Fintype.card ι : ℝ) ≤ ∑ k, ck k + (Fintype.card ι : ℝ) :=
      le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => hck0 k)
    have h3 : (Fintype.card ι : ℝ) * (CI * max CGam 1) ≤
        (∑ k, ck k + (Fintype.card ι : ℝ)) * (CI + CPi * max CGam 1) * max CGam 1 := by
      have h4 : (Fintype.card ι : ℝ) * CI ≤ (∑ k, ck k + (Fintype.card ι : ℝ)) *
          (CI + CPi * max CGam 1) :=
        mul_le_mul hcard (by nlinarith [mul_nonneg hCPi hmax]) hCI0
          (add_nonneg (Finset.sum_nonneg fun k _ => hck0 k) (Nat.cast_nonneg _))
      calc (Fintype.card ι : ℝ) * (CI * max CGam 1) = (Fintype.card ι : ℝ) * CI * max CGam 1 := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h4 hmax
    calc (Fintype.card ι : ℝ) * (CI * max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j))
        = (Fintype.card ι : ℝ) * (CI * max CGam 1) *
            parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hpow

end Model

end RegularityStructures

end
