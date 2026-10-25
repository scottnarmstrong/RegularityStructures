/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SupMainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Uniform bound on the polynomial components of `𝒦_γ f`, near-pair `Γ`-bounds

A single constant bounding all polynomial components `X^k`, `|k| < γ + 2`, of `𝒦_γ f(x)` on the
time slab, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- A single constant bounding all the polynomial components `X^k`, `|k| < γ + 2`, of `𝒦_γ f(x)`
(for fixed `N'`). -/
theorem exists_uniform_abs_kGammaS_apply_emb_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {N : ℕ} {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (hN : N' ≤ N)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      M.IsPolyCompatible P → ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
        (V : Submodule ℝ (ι → ℝ)), (∀ z, f z ∈ V) →
        (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) →
      ∀ {x : ParabolicSpace}, x ∈ timeSlab T → ∀ kk : PolyIndex N', polyDeg N' kk < γ + 2 →
      |M.kGammaS h P I γ f x (P.emb kk)| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk) := by
  classical
  have key : ∀ kk : PolyIndex N', ∃ C : ℝ, 0 ≤ C ∧
      (polyDeg N' kk < γ + 2 → ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      M.IsPolyCompatible P → ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
        (V : Submodule ℝ (ι → ℝ)), (∀ z, f z ∈ V) →
        (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) →
      ∀ {x : ParabolicSpace}, x ∈ timeSlab T →
      |M.kGammaS h P I γ f x (P.emb kk)| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk)) := by
    intro kk
    by_cases hk : polyDeg N' kk < γ + 2
    · have hk' : (multiDeg kk.1 : ℝ) < γ + 2 := hk
      obtain ⟨C, hC0, hC⟩ := exists_abs_kGammaS_apply_emb_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη hh hc kk.1 hk'
        P hN (hni kk.1 hk')
      exact ⟨C, hC0, fun _ M f T Cf CPi CGam S hM I V hfV hIp x hx =>
        hC M f T Cf CPi CGam S hM I V hfV hIp hx kk rfl⟩
    · exact ⟨0, le_rfl, fun hk' => absurd hk' hk⟩
  choose Ck hCk0 hCk using key
  refine ⟨∑ kk, Ck kk, Finset.sum_nonneg fun kk _ => hCk0 kk,
    fun M f T Cf CPi CGam S hM I V hfV hIp x hx kk hkk => ?_⟩
  have hle : Ck kk ≤ ∑ kk, Ck kk :=
    Finset.single_le_sum (f := Ck) (fun kk _ => hCk0 kk) (Finset.mem_univ kk)
  have hnn : 0 ≤ (max 1 CGam * CPi) * Cf *
      singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk) :=
    mul_nonneg (mul_nonneg S.hK0 S.hCf)
      (Real.rpow_nonneg (KGammaSup.weight_pos hx).le _)
  calc _ ≤ Ck kk * (max 1 CGam * CPi) * Cf *
        singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk) :=
        hCk kk hkk M f T Cf CPi CGam S hM I V hfV hIp hx
    _ = Ck kk * ((max 1 CGam * CPi) * Cf *
          singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk)) := by ring
    _ ≤ (∑ kk, Ck kk) * ((max 1 CGam * CPi) * Cf *
          singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk)) :=
        mul_le_mul_of_nonneg_right hle hnn
    _ = _ := by ring

end Model

end RegularityStructures

end
