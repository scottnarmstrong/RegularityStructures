/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.LinearShellWNear
public import RegularityStructures.Abstract.Singular.KGamma.SupMainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Linearity of `𝒦_γ`, near-pair `Γ`-bounds

Additivity and homogeneity of `nCoeffS`, `nVecS` and `kGammaS` in the modelled distribution `f`, for
models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ}
  {γ η α C₁ C₂ CPi CGam T : ℝ} {f f₁ f₂ : ParabolicSpace → ι → ℝ} {N' : ℕ} {P : PolynomialSector 𝒯 N'}

theorem nCoeffS_add_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S₁ : LayerSettingWNear M f₁ γ η α C₁ CPi CGam T) (S₂ : LayerSettingWNear M f₂ γ η α C₂ CPi CGam T)
    (k : Fin 4 →₀ ℕ) (hkγ : (multiDeg k : ℝ) < γ + 2) (hN : N' ≤ N)
    (hM : M.IsPolyCompatible P)
    (hni : ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ →
      (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.nCoeffS h (f₁ + f₂) x k = M.nCoeffS h f₁ x k + M.nCoeffS h f₂ x k := by
  have s₁ := summable_singShellPairing_win_near 𝒯 γ η α S₁.hdeg S₁.hγ S₁.hαγ S₁.hαη hh hc k hkγ P hN hni
    M f₁ T C₁ CPi CGam S₁ hM hx
  have s₂ := summable_singShellPairing_win_near 𝒯 γ η α S₁.hdeg S₁.hγ S₁.hαγ S₁.hαη hh hc k hkγ P hN hni
    M f₂ T C₂ CPi CGam S₂ hM hx
  unfold nCoeffS
  rw [← s₁.tsum_add s₂]
  exact tsum_congr fun n => singShellPairing_add_win_near hh hc S₁ S₂ k n hx

theorem nVecS_add_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S₁ : LayerSettingWNear M f₁ γ η α C₁ CPi CGam T) (S₂ : LayerSettingWNear M f₂ γ η α C₂ CPi CGam T)
    (hN : N' ≤ N) (hM : M.IsPolyCompatible P)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.nVecS h P γ (f₁ + f₂) x = M.nVecS h P γ f₁ x + M.nVecS h P γ f₂ x := by
  classical
  unfold nVecS
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun kk _ => ?_
  by_cases hk : polyDeg N' kk < γ + 2
  · have hk' : (multiDeg kk.1 : ℝ) < γ + 2 := hk
    simp only [hk, ite_true]
    rw [nCoeffS_add_win_near hh hc S₁ S₂ kk.1 hk' hN hM (hni kk.1 hk') hx, add_div, add_smul]
  · simp [hk]

theorem kGammaS_add_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S₁ : LayerSettingWNear M f₁ γ η α C₁ CPi CGam T) (S₂ : LayerSettingWNear M f₂ γ η α C₂ CPi CGam T)
    (hN : N' ≤ N) (hM : M.IsPolyCompatible P)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.kGammaS h P I γ (f₁ + f₂) x = M.kGammaS h P I γ f₁ x + M.kGammaS h P I γ f₂ x := by
  unfold kGammaS
  rw [Pi.add_apply, map_add, map_add, nVecS_add_win_near hh hc S₁ S₂ hN hM hni hx]
  abel

theorem nCoeffS_smul_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S : LayerSettingWNear M f γ η α C₁ CPi CGam T) (c : ℝ) (k : Fin 4 →₀ ℕ)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.nCoeffS h (c • f) x k = c * M.nCoeffS h f x k := by
  unfold nCoeffS
  rw [← tsum_mul_left]
  exact tsum_congr fun n => singShellPairing_smul_win_near hh hc S c k n hx

theorem nVecS_smul_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S : LayerSettingWNear M f γ η α C₁ CPi CGam T) (c : ℝ)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.nVecS h P γ (c • f) x = c • M.nVecS h P γ f x := by
  classical
  unfold nVecS
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun kk _ => ?_
  by_cases hk : polyDeg N' kk < γ + 2
  · simp only [hk, ite_true]
    rw [nCoeffS_smul_win_near hh hc S c kk.1 hx, smul_smul, mul_div_assoc]
  · simp [hk]

theorem kGammaS_smul_win_near (hh : ShellProfile h N)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S : LayerSettingWNear M f γ η α C₁ CPi CGam T) (c : ℝ)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.kGammaS h P I γ (c • f) x = c • M.kGammaS h P I γ f x := by
  unfold kGammaS
  rw [Pi.smul_apply, map_smul, map_smul, nVecS_smul_win_near hh hc S c hx, smul_add, smul_add]

end Model

end RegularityStructures

end
