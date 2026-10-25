/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesBigWNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesLargeWNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesTauWNear
public import RegularityStructures.Abstract.Singular.KGamma.SeriesTaylorWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Singular.KGamma.Bracket
public import RegularityStructures.Abstract.Singular.KGamma.SeriesAux
public import RegularityStructures.Abstract.Singular.KGamma.SeriesBig
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# Large-scale terms of the polynomial series of `𝒦_γ f`, near-pair `Γ`-bounds

At the large scales `2^{-n} ≥ d`, `|polyUS n| ≤ C K₀ C_f d^σ W^{α∧η−γ} s^a` with `s = 2^n d ≤ 1`,
for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N N' : ℕ}
  {h : ParabolicSpace → ℝ}

open Classical in
/-- **Large scales** `2^{-n} ≥ d`: `|polyUS n| ≤ C K₀ C_f d^σ W^{α∧η−γ} s^a`, `s = 2^n d ≤ 1`. -/
theorem exists_abs_polyUS_le_of_le_one_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (hN : N' ≤ N) (k : Fin 4 →₀ ℕ)
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η α : ℝ) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hαγ : α ≤ γ) (hαη : -2 < min α η)
    (hkγ : (multiDeg k : ℝ) < γ + 2)
    (hnat : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k)
    (P : PolynomialSector 𝒯 N') {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hni : ∀ i, i ∉ Set.range P.emb → (Pi.single i 1 : ι → ℝ) ∈ V → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T → M.IsPolyCompatible P →
      (∀ z, f z ∈ V) → ∀ {x y : ParabolicSpace}, SlabPair T x y → ∀ n : ℕ,
      (2 : ℝ) ^ n * parabolicNorm (y - x) ≤ 1 →
      |polyUS M h γ f x y k n| ≤
        C * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^ (min α η - γ)) *
            ((2 : ℝ) ^ n * parabolicNorm (y - x)) ^ a := by
  have hσ : 0 < γ + 2 - (multiDeg k : ℝ) := by linarith
  set σ : ℝ := γ + 2 - multiDeg k with hσdef
  set σ' : ℝ := (⌈σ⌉ : ℝ) with hσ'def
  have hlt : σ < σ' := lt_ceil_of_forall_multiDeg_ne hσ hnat
  have hσ' : 0 < σ' := hσ.trans hlt
  obtain ⟨a₂, C₂, ha₂, hC₂, H₂⟩ := exists_abs_sum_tau_pairing_ge_le_win_near hh hN k 𝒯 η α hdeg P hV hVb hni
  obtain ⟨Cb, hCb0, Hb⟩ := Model.exists_abs_latticeRecon_sub_pairing_dTaylor_le_win_near hh hc k hσ' 𝒯 η
    hγ hdeg
  obtain ⟨Cl, hCl0, Hl⟩ := exists_abs_latticeRecon_dTaylor_big_le_win_near hh hc k hσ' 𝒯 γ η α hdeg hγ hαγ
    hαη
  obtain ⟨Cq, hCq0, Hq⟩ := exists_abs_pairing_fx_dTaylor_le_win_near hh k hσ' 𝒯 η α hdeg
  refine ⟨min a₂ (σ' - σ), C₂ + Cb * 2 ^ |η - γ| + Cl + Cq, lt_min ha₂ (by linarith),
    by positivity, fun M f T Cf CPi CGam S hpoly hfV x y Pr n hs => ?_⟩
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hCf := S.hCf
  have hd := Pr.hd
  have hW := Pr.W_pos
  have hW1 := Pr.W_le_one
  have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  set W := min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with hWdef
  set s : ℝ := (2 : ℝ) ^ n * parabolicNorm (y - x) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  set a : ℝ := min a₂ (σ' - σ) with hadef
  set Y : ℝ := (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ * W ^ (min α η - γ)) *
    s ^ a with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hdn : parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹ := by
    calc parabolicNorm (y - x) = s * ((2 : ℝ) ^ n)⁻¹ := by rw [hsdef]; field_simp
      _ ≤ 1 * ((2 : ℝ) ^ n)⁻¹ := mul_le_mul_of_nonneg_right hs (inv_nonneg.2 hu.le)
      _ = _ := one_mul _
  have hsq : s ^ (σ' - σ) ≤ s ^ a := rpow_le_of_le_one hs0 hs (min_le_right _ _)
  have hconv : parabolicNorm (y - x) ^ σ' * ((2 : ℝ) ^ n) ^ (σ' + multiDeg k - 2 - γ) =
      parabolicNorm (y - x) ^ σ * s ^ (σ' - σ) := by
    have hq : σ' + multiDeg k - 2 - γ = σ' - σ := by rw [hσdef]; ring
    rw [hq, rpow_mul_rpow_scale hd hu σ' (σ' - σ)]
    congr 2; ring
  -- the `τ`-terms
  have hT2 := H₂ M f T Cf CPi CGam S hpoly hfV Pr n hs
  have hT2' : |∑ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2),
      (f y - M.gammaMap y x (f x)) i * parabolicSemigroup.pairing
        (fun t z => M.regPi y (Pi.single i 1) t z)
        (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))| ≤ C₂ * Y := by
    refine hT2.trans ?_
    have h1 : s ^ a₂ ≤ s ^ a := rpow_le_of_le_one hs0 hs (min_le_left _ _)
    have h2 : W ^ (η - γ) ≤ W ^ (min α η - γ) := rpow_le_rpow_min hW hW1
    have hX : 0 ≤ C₂ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ * W ^ (η - γ)) := by
      positivity
    calc _ ≤ C₂ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ * W ^ (η - γ)) * s ^ a :=
          mul_le_mul_of_nonneg_left h1 hX
      _ ≤ C₂ * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ * W ^ (min α η - γ)) *
          s ^ a := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs0.le _)
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2
            (Real.rpow_nonneg hd.le _)) (by positivity)
      _ = C₂ * Y := by rw [hY]; ring
  -- the large form
  have hlarge := Model.polyUS_eq_large_of_slab_win_near hh hc S Pr.hx Pr.hy k n
  rw [← dTaylorKernel_ceil h k n σ x y] at hlarge
  rw [hlarge]
  refine (abs_sub _ _).trans ?_
  have hRP : |M.latticeRecon f (dTaylorKernel h k n σ' x y) -
      parabolicSemigroup.pairing (M.regPi x (f x)) (dTaylorKernel h k n σ' x y)| ≤
      (Cb * 2 ^ |η - γ| + Cl + Cq) * Y := by
    by_cases hB : 128 * ((2 : ℝ) ^ n)⁻¹ ≤ W
    · -- local bound
      have hn : 1 ≤ n := by
        by_contra hn0
        have : n = 0 := by omega
        subst this
        simp at hB
        linarith
      have hb := Hb M n hn S.hPi S.hCPi S.hGam S.hgrowth S.hT S.hfT S.hf Pr.hx Pr.hy.2 hd hdn
        (hB.trans Pr.W_le_x)
      rw [hconv] at hb
      have hwx := rpow_weight_le hW Pr.W_le_x Pr.x_le_two_W (η - γ)
      have h2 : W ^ (η - γ) ≤ W ^ (min α η - γ) := rpow_le_rpow_min hW hW1
      have hX : 0 ≤ Cb * (max 1 CGam * CPi) * Cf := by positivity
      calc _ ≤ Cb * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ * s ^ (σ' - σ)) *
            singularWeight timeZeroDist x ^ (η - γ) := hb
        _ ≤ Cb * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ * s ^ a) *
            (2 ^ |η - γ| * W ^ (min α η - γ)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq
              (Real.rpow_nonneg hd.le _)) hX) (hwx.trans
              (mul_le_mul_of_nonneg_left h2 (by positivity)))
              (Real.rpow_nonneg Pr.weight_x_pos.le _) (by positivity)
        _ = (Cb * 2 ^ |η - γ|) * Y := by rw [hY]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [hCl0, hCq0]) hY0
    · have h128 : (2 : ℝ) ^ n * W ≤ 128 := by
        have h1 := mul_lt_mul_of_pos_left (lt_of_not_ge hB) hu
        have h2 : (2 : ℝ) ^ n * (128 * ((2 : ℝ) ^ n)⁻¹) = 128 := by field_simp
        linarith
      have hR := Hl M f T Cf CPi CGam S Pr n hdn h128
      have hQ := Hq M f T Cf CPi CGam S Pr n hdn h128
      rw [hconv] at hR hQ
      have hW0 := Real.rpow_nonneg hW.le (min α η - γ)
      have hz : ∀ c : ℝ, 0 ≤ c → c * (max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ *
          s ^ (σ' - σ)) * W ^ (min α η - γ) ≤ c * Y := by
        intro c hc0
        calc _ = c * ((max 1 CGam * CPi) * Cf * (parabolicNorm (y - x) ^ σ * W ^ (min α η - γ)) *
              s ^ (σ' - σ)) := by ring
          _ ≤ c * Y := by
            refine mul_le_mul_of_nonneg_left ?_ hc0
            rw [hY]
            exact mul_le_mul_of_nonneg_left hsq (by positivity)
      refine (abs_sub _ _).trans ?_
      have := add_le_add (hR.trans (hz Cl hCl0)) (hQ.trans (hz Cq hCq0))
      refine this.trans ?_
      have : 0 ≤ Cb * 2 ^ |η - γ| := by positivity
      linarith [mul_nonneg this hY0]
  calc _ ≤ _ := add_le_add hRP hT2'
    _ = _ := by rw [hY]; ring

end RegularityStructures

end
