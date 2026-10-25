/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesWNear
public import RegularityStructures.Abstract.Singular.KGamma.SupMainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.IncrementWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Theorem71.BracketPtG

/-!
# Increments of the polynomial components of `𝒦_γ f` for close pairs, near-pair `Γ`-bounds

For a causal shell profile `h` and `x, y` in the time slab with `64 d(y, x) ≤ W = min(w(x), w(y))`,
the `X^k` component of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` is bounded by
`C (max 1 C_Γ · C_Π) C_f d^{γ+2−|k|} W^{α∧η−γ}` [Hai14, Proposition 6.16]
(`exists_abs_kGammaS_sub_gamma_apply_emb_le_close_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N N' : ℕ}

namespace Model

/-- **Close pairs, polynomial components** [Hai14, Prop. 6.16], window models, causal shell
profile `h`. -/
theorem exists_abs_kGammaS_sub_gamma_apply_emb_le_close_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (hN : N' ≤ N) (P : PolynomialSector 𝒯 N')
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
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), M.IsRealisingP h γ P I V →
        IsAbstractIntegration P V I 2 → (∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0) →
        (∀ z, f z ∈ V) → ∀ {x y : ParabolicSpace}, x ∈ timeSlab T → y ∈ timeSlab T →
        0 < parabolicNorm (y - x) →
        64 * parabolicNorm (y - x) ≤
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) →
      |(M.kGammaS h P I γ f y -
          M.gammaMap y x (M.kGammaS h P I γ f x)) (P.emb kk)| ≤
        C * (max 1 CGam * CPi) * Cf * parabolicNorm (y - x) ^ (γ + 2 - polyDeg N' kk) *
          min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) ^
            (min α η - γ) := by
  have hk' : (multiDeg kk.1 : ℝ) < γ + 2 := hk
  have hnie : ∀ i, i ∉ Set.range P.emb → (Pi.single i 1 : ι → ℝ) ∈ V → 𝒯.deg i < γ →
      (multiDeg kk.1 : ℝ) ≠ 𝒯.deg i + 2 :=
    fun i hp hiV hi => hni kk.1 hk' i hp (hVα i hiV) hi
  obtain ⟨C, hC0, hC⟩ := exists_abs_tsum_polyUS_le_win_near hh hc hN kk.1 𝒯 η α hγ hdeg hαγ hαη hk'
    (hnat kk.1 hk') P hV hVb hnie
  refine ⟨C, hC0, fun M f T Cf CPi CGam S I hreal hInt hIp hfV x y hx hy hd hW => ?_⟩
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  obtain ⟨-, hb⟩ := hC M f T Cf CPi CGam S hreal.poly hfV hx hy hd hW
  have hdeg2 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j :=
    fun j hjV _ => by linarith [hVα j hjV, min_le_left α η]
  have hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
      ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N' :=
    fun j _ hj k hkj => hNγ k (by linarith)
  have hSy := summable_singShellPairing_win_near 𝒯 γ η α hdeg hγ hαγ hαη hh hc kk.1 hk' P hN
    (hni kk.1 hk') M f T Cf CPi CGam S hreal.poly hy
  have hSe : ∀ l ∈ taylorIdx (γ + 2 - multiDeg kk.1), Summable fun n =>
      M.singShellPairing h f x (kk.1 + l) n := by
    intro l hl
    have hl' := (mem_taylorIdx_iff l).1 hl
    have hkl : (multiDeg (kk.1 + l) : ℝ) < γ + 2 := by
      have : multiDeg (kk.1 + l) = multiDeg kk.1 + multiDeg l := map_add _ _ _
      rw [this]; push_cast; linarith
    exact summable_singShellPairing_win_near 𝒯 γ η α hdeg hγ hαγ hαη hh hc (kk.1 + l) hkl P hN
      (hni _ hkl) M f T Cf CPi CGam S hreal.poly hx
  obtain ⟨-, heq⟩ := poly_bracketS_of_summable_growth hh hreal hInt hV hVb hdeg2 G hN'
    hNγ hIp S.hfT hfV x y kk hSy hSe hk
  have hf1 : (1 : ℝ) ≤ multiFactorial kk.1 := by exact_mod_cast multiFactorial_pos kk.1
  have habs : |(M.kGammaS h P I γ f y -
      M.gammaMap y x (M.kGammaS h P I γ f x)) (P.emb kk)| ≤
        |∑' n, polyUS M h γ f x y kk.1 n| := by
    rw [← heq, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ multiFactorial kk.1)]
    exact le_mul_of_one_le_right (abs_nonneg _) hf1
  exact habs.trans hb

end Model

end RegularityStructures

end
