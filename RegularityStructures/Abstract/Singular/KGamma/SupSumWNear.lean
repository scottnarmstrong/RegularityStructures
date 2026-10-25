/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SupTermWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Abstract.Singular.KGamma.Geom
public import RegularityStructures.Abstract.Singular.KGamma.SupTerm
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Sup bound for the `X^k` series of `𝒦_γ f`, near-pair `Γ`-bounds

Summability and the sup bound of the series over scales `n` of the shell terms that make up the
`X^k` component of `𝒦_γ f`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}
  {h : ParabolicSpace → ℝ}

namespace Model

variable (hh : ShellProfile h N) (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
  (k : Fin 4 →₀ ℕ)

include hh hc in
/-- **Sup bound for the `X^k` series**. -/
theorem exists_summable_abs_tsum_shellTerm_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) (hkγ : (multiDeg k : ℝ) < γ + 2)
    {N' : ℕ} (P : PolynomialSector 𝒯 N') (hN : N' ≤ N)
    (hni : ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T → M.IsPolyCompatible P →
      ∀ {x : ParabolicSpace}, x ∈ timeSlab T →
      Summable (fun n => M.shellTerm h f x k n) ∧
      |∑' n, M.shellTerm h f x k n| ≤
        C * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - multiDeg k) := by
  obtain ⟨a, b, C, ha, hb, hC0, hC⟩ := exists_abs_shellTerm_le_win_near hh hc k 𝒯 γ η α hdeg hγ hαγ hαη
    hkγ P hN hni
  obtain ⟨Cg, hCg0, hCg⟩ := KGammaSup.exists_summable_abs_tsum_le a b ha hb
  refine ⟨Cg * C, mul_nonneg hCg0 hC0, fun M f T Cf CPi CGam S hM x hx => ?_⟩
  have hw := KGammaSup.weight_pos hx
  have hK0 : 0 ≤ C * (max 1 CGam * CPi) * Cf *
      singularWeight timeZeroDist x ^ (min α η + 2 - multiDeg k) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 S.hK0) S.hCf) (Real.rpow_nonneg hw.le _)
  obtain ⟨hs, hb'⟩ := hCg _ hw (fun n => M.shellTerm h f x k n) _ hK0 (fun n => hC M f T Cf CPi
    CGam S hM hx n)
  have hs' : Summable (fun n => M.shellTerm h f x k n) := hs
  refine ⟨hs', ?_⟩
  have h1 : |∑' n, M.shellTerm h f x k n| ≤ ∑' n, |M.shellTerm h f x k n| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs'.norm
  exact h1.trans (hb'.trans (le_of_eq (by ring)))

end Model

end RegularityStructures

end
