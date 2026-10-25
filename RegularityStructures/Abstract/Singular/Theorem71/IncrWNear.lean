/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.FarAllWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.IncrementWNear
public import RegularityStructures.Abstract.Singular.Theorem71.CloseWNear
public import RegularityStructures.Abstract.Singular.Theorem71.IncrNonpolyWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# Increments of the polynomial components of `𝒦_γ f + R_γ f`, near-pair `Γ`-bounds

For a kernel pair `(h, r)`, `F = 𝒦_γ f + R_γ f`, `x, y` in the time slab with
`d = d(y, x) ≤ W = min(w(x), w(y))`, and `|k| < γ + 2`,
`|(F(y) − Γ_{yx} F(x))_{X^k}| ≤ C K₁ C_f d^{γ+2−|k|} W^{α∧η−γ}` with
`K₁ = (max 1 C_Γ C_Π + |ι| C_I) max 1 C_{Γ,2}`, for close and far pairs
(`exists_abs_kGammaRemG_sub_gamma_apply_emb_le_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N N' : ℕ}

private theorem eq_of_parabolicNorm_sub_eq_zero_W {x y : ParabolicSpace}
    (h : parabolicNorm (y - x) = 0) : y = x := by
  unfold parabolicNorm at h
  have h1 : 0 ≤ Real.sqrt |(y - x).1| := Real.sqrt_nonneg _
  have h2 : 0 ≤ ∑ i, |(y - x).2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h3 : Real.sqrt |(y - x).1| = 0 := by linarith
  have h4 : ∑ i, |(y - x).2 i| = 0 := by linarith
  have h5 : (y - x).1 = 0 := by
    have := (Real.sqrt_eq_zero (abs_nonneg _)).1 h3
    exact abs_eq_zero.1 this
  have h6 : ∀ i, (y - x).2 i = 0 := fun i =>
    abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg _).1 h4 i
      (Finset.mem_univ i))
  have e : y - x = 0 := Prod.ext h5 (funext h6)
  exact sub_eq_zero.1 e

namespace Model

/-- Increments of the polynomial components of `𝒦_γ f + R_γ f`, close and far pairs. -/
theorem exists_abs_kGammaRemG_sub_gamma_apply_emb_le_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N) (hN : N' ≤ N)
    (P : PolynomialSector 𝒯 N')
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N')
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hVα : ∀ i, (Pi.single i 1 : ι → ℝ) ∈ V → α ≤ 𝒯.deg i)
    (kk : PolyIndex N') (hk : polyDeg N' kk < γ + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam CI CΓ2 : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), M.IsRealisingP h γ P I V →
        IsAbstractIntegration P V I 2 → (∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0) →
        (∀ i j, |I (Pi.single i 1) j| ≤ CI) → (∀ z, f z ∈ V) →
        M.GammaNearOn (γ + 2) CΓ2 (timeSlab T) →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab T → y ∈ timeSlab T →
        parabolicNorm (y - x) ≤
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) →
      |(M.kGammaRemG h r P I γ f y -
          M.gammaMap y x (M.kGammaRemG h r P I γ f x))
          (P.emb kk)| ≤
        C * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ2) * Cf *
          (parabolicNorm (y - x) ^ (γ + 2 - polyDeg N' kk) *
            min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
              (min α η - γ)) := by
  have hh := hp.shell
  have hc := hp.causal
  obtain ⟨Cc, hCc0, hCc⟩ := exists_abs_kGammaS_sub_gamma_apply_emb_le_close_win_near 𝒯 γ η α hdeg hγ hαγ
    hαη hh hc hN P hNγ hnat hni hV hVb hVα kk hk
  obtain ⟨Cr, hCr0, hCr⟩ := exists_abs_remVec_sub_gammaMap_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη hp.rem P hNγ
    kk hk
  obtain ⟨Cn, hCn0, hCn⟩ := exists_abs_kGammaS_sub_gamma_apply_le_far_win_near 𝒯 γ η α hdeg hγ hαγ hαη hh
    hc P hN hni
  refine ⟨Cc + Cr + Cn, by positivity, fun M f T Cf CPi CGam CI CΓ2 S I hreal hInt hIp hCI hfV
    hΓ2 x y hx hy hdW => ?_⟩
  have hdeg2 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j :=
    fun j hjV _ => by linarith [hVα j hjV, min_le_left α η]
  have hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
      ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N' :=
    fun j _ hj k hkj => hNγ k (by linarith)
  have hsplit : M.kGammaRemG h r P I γ f y -
      M.gammaMap y x (M.kGammaRemG h r P I γ f x) =
      (M.kGammaS h P I γ f y -
        M.gammaMap y x (M.kGammaS h P I γ f x)) +
      (M.remVecG r P γ f y - M.gammaMap y x (M.remVecG r P γ f x)) := by
    unfold kGammaRemG
    rw [map_add]; abel
  set d : ℝ := parabolicNorm (y - x) with hd
  set W : ℝ := min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with hW
  set σ : ℝ := γ + 2 - polyDeg N' kk with hσ
  set e : ℝ := min α η - γ with he
  set K₀ : ℝ := max 1 CGam * CPi with hK₀
  set K₁ : ℝ := (K₀ + Fintype.card ι * CI) * max 1 CΓ2 with hK₁
  have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI (P.emb kk) (P.emb kk))
  have hK₀0 : 0 ≤ K₀ := S.hK0
  have hcI : 0 ≤ (Fintype.card ι : ℝ) * CI := mul_nonneg (Nat.cast_nonneg _) hCI0
  have hG : (1 : ℝ) ≤ max 1 CΓ2 := le_max_left _ _
  have hK₁0 : 0 ≤ K₁ := mul_nonneg (add_nonneg hK₀0 hcI) (zero_le_one.trans hG)
  have hK₀₁ : K₀ ≤ K₁ := by
    have : K₀ + Fintype.card ι * CI ≤ (K₀ + Fintype.card ι * CI) * max 1 CΓ2 :=
      le_mul_of_one_le_right (add_nonneg hK₀0 hcI) hG
    linarith
  have hWpos : 0 < W := lt_min (KGammaSup.weight_pos hx) (KGammaSup.weight_pos hy)
  have hW1 : W ≤ 1 := (min_le_left _ _).trans (singularWeight_le_one _ _)
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hCf := S.hCf
  have hX0 : 0 ≤ d ^ σ * W ^ e := mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hWpos.le _)
  have hY0 : 0 ≤ K₁ * Cf * (d ^ σ * W ^ e) := mul_nonneg (mul_nonneg hK₁0 hCf) hX0
  have hCC : 0 ≤ Cc + Cr + Cn := by positivity
  rcases eq_or_lt_of_le hd0 with hdz | hdp
  · -- `x = y`
    have hxy : y = x := eq_of_parabolicNorm_sub_eq_zero_W hdz.symm
    rw [hxy, M.gammaMap_self]
    simp only [LinearMap.id_apply, sub_self, Pi.zero_apply, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCC hK₁0) hCf) hX0
  · -- `d > 0`
    have hdW1 : parabolicNorm (y - x) ≤ 1 := hdW.trans (hW1)
    have hRb := hCr M f T Cf CPi CGam S hreal.poly x y hx.2 hy.2 hdW1
    have hWe : 1 ≤ W ^ e := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hWpos hW1
      (by rw [he]; linarith [min_le_left α η])
    have hR : |(M.remVecG r P γ f y - M.gammaMap y x (M.remVecG r P γ f x)) (P.emb kk)| ≤
        Cr * (K₁ * Cf * (d ^ σ * W ^ e)) := by
      refine hRb.trans ?_
      have h1 : Cr * K₀ * Cf * d ^ σ ≤ Cr * K₀ * Cf * (d ^ σ * W ^ e) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.rpow_nonneg hd0 _) hWe)
          (mul_nonneg (mul_nonneg hCr0 hK₀0) hCf)
      refine h1.trans ?_
      have h2 : K₀ * (Cf * (d ^ σ * W ^ e)) ≤ K₁ * (Cf * (d ^ σ * W ^ e)) :=
        mul_le_mul_of_nonneg_right hK₀₁ (mul_nonneg hCf hX0)
      calc Cr * K₀ * Cf * (d ^ σ * W ^ e) = Cr * (K₀ * (Cf * (d ^ σ * W ^ e))) := by ring
        _ ≤ Cr * (K₁ * (Cf * (d ^ σ * W ^ e))) := mul_le_mul_of_nonneg_left h2 hCr0
        _ = _ := by ring
    have hK : |(M.kGammaS h P I γ f y -
        M.gammaMap y x (M.kGammaS h P I γ f x)) (P.emb kk)| ≤
        (Cc + Cn) * (K₁ * Cf * (d ^ σ * W ^ e)) := by
      by_cases h64 : 64 * d ≤ W
      · have hb := hCc M f T Cf CPi CGam S I hreal hInt hIp hfV hx hy hdp h64
        have h2 : K₀ * (Cf * (d ^ σ * W ^ e)) ≤ K₁ * (Cf * (d ^ σ * W ^ e)) :=
          mul_le_mul_of_nonneg_right hK₀₁ (mul_nonneg hCf hX0)
        have h3 : Cc * (K₀ * (Cf * (d ^ σ * W ^ e))) ≤ Cc * (K₁ * (Cf * (d ^ σ * W ^ e))) :=
          mul_le_mul_of_nonneg_left h2 hCc0
        have h4 : Cc * (K₁ * (Cf * (d ^ σ * W ^ e))) ≤ (Cc + Cn) * (K₁ * Cf * (d ^ σ * W ^ e)) := by
          have : Cc * (K₁ * Cf * (d ^ σ * W ^ e)) ≤ (Cc + Cn) * (K₁ * Cf * (d ^ σ * W ^ e)) :=
            mul_le_mul_of_nonneg_right (by linarith) hY0
          linarith [this, show Cc * (K₁ * (Cf * (d ^ σ * W ^ e))) =
            Cc * (K₁ * Cf * (d ^ σ * W ^ e)) by ring]
        refine hb.trans ?_
        calc _ = Cc * (K₀ * (Cf * (d ^ σ * W ^ e))) := by ring
          _ ≤ _ := h3.trans h4
      · have hW64 : W ≤ 64 * d := (not_le.1 h64).le
        have hj : 𝒯.deg (P.emb kk) < γ + 2 := by rw [P.deg_emb]; exact hk
        have hb := hCn M f T Cf CPi CGam S I V hfV hreal hInt hV hVb hdeg2 hN' hIp hCI hΓ2 hx hy
          hdW hW64 (P.emb kk) hj
        rw [P.deg_emb] at hb
        have hsd : parabolicSemigroup.scaleDist y x = d := rfl
        rw [hsd] at hb
        refine hb.trans ?_
        have : Cn * (K₁ * Cf * (d ^ σ * W ^ e)) ≤ (Cc + Cn) * (K₁ * Cf * (d ^ σ * W ^ e)) :=
          mul_le_mul_of_nonneg_right (by linarith) hY0
        refine le_trans (le_of_eq ?_) this
        rw [hK₁, hK₀]; ring
    rw [hsplit, Pi.add_apply]
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ (Cc + Cn) * (K₁ * Cf * (d ^ σ * W ^ e)) + Cr * (K₁ * Cf * (d ^ σ * W ^ e)) :=
          add_le_add hK hR
      _ = _ := by ring

end Model

end RegularityStructures

end
