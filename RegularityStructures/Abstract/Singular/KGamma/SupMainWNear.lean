/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SupSumWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.SupCoeffG
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Sup bound for the polynomial components of `𝒦_γ f`, near-pair `Γ`-bounds

Absolute convergence of the series of `nCoeffS` and the sup bound on the polynomial components `X^k`
of `𝒦_γ f` on the time slab [Hai14, Proposition 6.16], for models whose `Γ`-bounds hold only for
near pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- The series of `nCoeffS` converges absolutely. -/
theorem summable_singShellPairing_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {N : ℕ} {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)
    (hkγ : (multiDeg k : ℝ) < γ + 2) {N' : ℕ} (P : PolynomialSector 𝒯 N') (hN : N' ≤ N)
    (hni : ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ) (T Cf CPi CGam : ℝ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (hM : M.IsPolyCompatible P) {x : ParabolicSpace}
    (hx : x ∈ timeSlab T) :
    Summable (fun n => M.singShellPairing h f x k n) := by
  obtain ⟨C, -, hC⟩ := exists_summable_abs_tsum_shellTerm_le_win_near hh hc k 𝒯 γ η α hdeg hγ hαγ hαη hkγ
    P hN hni
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  exact summable_singShellPairing_of_shellTerm_growth M hh G S.hdeg (S.hfT x) k
    (hC M f T Cf CPi CGam S hM hx).1

/-- **Sup bound for the polynomial components `X^k` of `𝒦_γ f`**. -/
theorem exists_abs_kGammaS_apply_emb_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {N : ℕ} {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)
    (hkγ : (multiDeg k : ℝ) < γ + 2) {N' : ℕ} (P : PolynomialSector 𝒯 N') (hN : N' ≤ N)
    (hni : ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → M.IsPolyCompatible P →
      ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
        (V : Submodule ℝ (ι → ℝ)), (∀ z, f z ∈ V) →
        (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) →
      ∀ {x : ParabolicSpace}, x ∈ timeSlab T → ∀ kk : PolyIndex N', kk.1 = k →
      |M.kGammaS h P I γ f x (P.emb kk)| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - multiDeg k) := by
  obtain ⟨C, hC0, hC⟩ := exists_summable_abs_tsum_shellTerm_le_win_near hh hc k 𝒯 γ η α hdeg hγ hαγ hαη
    hkγ P hN hni
  refine ⟨C, hC0, fun M f T Cf CPi CGam S hM I V hfV hIp x hx kk hkk => ?_⟩
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  subst hkk
  obtain ⟨hsum, hb⟩ := hC M f T Cf CPi CGam S hM hx
  rw [kGammaS_apply_emb_growth M hh G S.hdeg P I (S.hfT x) kk (hIp _ (hfV x) kk) hkγ
    hsum]
  have hfac : (1 : ℝ) ≤ multiFactorial kk.1 := by exact_mod_cast multiFactorial_pos kk.1
  rw [abs_div, abs_of_pos (lt_of_lt_of_le one_pos hfac)]
  exact (div_le_self (abs_nonneg _) hfac).trans hb

end Model

end RegularityStructures

end
