/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.LinearKGammaWNear
public import RegularityStructures.Abstract.Singular.KGamma.MeasKGammaSWNear
public import RegularityStructures.Abstract.Singular.KGamma.SupMainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.MeasWNear
public import RegularityStructures.Abstract.Singular.Theorem71.RemLinearWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Singular.Phi4FixedPointOperatorWeighted
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# The slab operator of the `Φ⁴₃` fixed point for a kernel pair, near-pair `Γ`-bounds

Additivity and homogeneity of `𝒦_γ + R_γ` at points of the slab (`kGammaRemG_add_win_near`,
`kGammaRemG_smul_win_near`) and of its slab restriction `kGammaRemGSlab`, and measurability of
`1_{(0,T]×ℝ³} (𝒦_γ f + R_γ f)` (`measurable_kGammaRemGSlab_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ η α C₁ C₂ CPi CGam T : ℝ}
  {f f₁ f₂ : ParabolicSpace → ι → ℝ} {N N' : ℕ} {P : PolynomialSector 𝒯 N'}
  {h r : ParabolicSpace → ℝ}

/-- The integration operator `𝒦_γ + R_γ` is additive in `f` at points of the slab. -/
theorem kGammaRemG_add_win_near (hp : KernelPair h r N)
    (S₁ : LayerSettingWNear M f₁ γ η α C₁ CPi CGam T) (S₂ : LayerSettingWNear M f₂ γ η α C₂ CPi CGam T)
    (hN : N' ≤ N) (hM : M.IsPolyCompatible P)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.kGammaRemG h r P I γ (f₁ + f₂) x =
      M.kGammaRemG h r P I γ f₁ x + M.kGammaRemG h r P I γ f₂ x := by
  unfold kGammaRemG
  rw [kGammaS_add_win_near hp.shell hp.causal S₁ S₂ hN hM hni I hx,
    remVecG_add_win_near S₁ S₂ hp.rem hx.2]
  abel

/-- The integration operator `𝒦_γ + R_γ` is homogeneous in `f` at points of the slab. -/
theorem kGammaRemG_smul_win_near (hp : KernelPair h r N)
    (S : LayerSettingWNear M f γ η α C₁ CPi CGam T) (c : ℝ) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    M.kGammaRemG h r P I γ (c • f) x = c • M.kGammaRemG h r P I γ f x := by
  unfold kGammaRemG
  rw [kGammaS_smul_win_near hp.shell hp.causal S c I hx, remVecG_smul_win_near S hp.rem c hx.2, smul_add]

theorem kGammaRemGSlab_add_win_near (hp : KernelPair h r N)
    (S₁ : LayerSettingWNear M f₁ γ η α C₁ CPi CGam T) (S₂ : LayerSettingWNear M f₂ γ η α C₂ CPi CGam T)
    (hN : N' ≤ N) (hM : M.IsPolyCompatible P)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    M.kGammaRemGSlab h r P I γ T (f₁ + f₂) =
      M.kGammaRemGSlab h r P I γ T f₁ + M.kGammaRemGSlab h r P I γ T f₂ := by
  funext x
  by_cases hx : x ∈ timeSlab T
  · simp only [Pi.add_apply, kGammaRemGSlab_of_mem I hx]
    exact kGammaRemG_add_win_near hp S₁ S₂ hN hM hni I hx
  · simp [kGammaRemGSlab_of_notMem I hx]

theorem kGammaRemGSlab_smul_win_near (hp : KernelPair h r N)
    (S : LayerSettingWNear M f γ η α C₁ CPi CGam T) (c : ℝ) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    M.kGammaRemGSlab h r P I γ T (c • f) = c • M.kGammaRemGSlab h r P I γ T f := by
  funext x
  by_cases hx : x ∈ timeSlab T
  · simp only [Pi.smul_apply, kGammaRemGSlab_of_mem I hx]
    exact kGammaRemG_smul_win_near hp S c I hx
  · simp [kGammaRemGSlab_of_notMem I hx]

/-- **Measurability of `1_{(0,T]×ℝ³} (𝒦_γ f + R_γ f)`** for a kernel pair `(h, r)` and `f`
satisfying the window layer setting. -/
theorem measurable_kGammaRemGSlab_win_near (hp : KernelPair h r N)
    (S : LayerSettingWNear M f γ η α C₁ CPi CGam T)
    (hJ : M.IsJointMeasurable) (hfm : Measurable f)
    (hN : N' ≤ N) (hM : M.IsPolyCompatible P)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    Measurable (M.kGammaRemGSlab h r P I γ T f) := by
  have hK := measurable_indicator_kGammaS_of_lt_win_near (P := P) hJ hp.shell hp.causal S hfm
    (fun x hx k hk => summable_singShellPairing_win_near 𝒯 γ η α S.hdeg S.hγ S.hαγ S.hαη
      hp.shell hp.causal k hk P hN (hni k hk) M f T C₁ CPi CGam S hM hx) I
  have hR := measurable_indicator_timeSlab_remVec_win_near S hp.rem P
  have e : M.kGammaRemGSlab h r P I γ T f = fun x =>
      (timeSlab T).indicator (fun x => M.kGammaS h P I γ f x) x +
        (timeSlab T).indicator (M.remVecG r P γ f) x := by
    funext x
    by_cases hx : x ∈ timeSlab T
    · simp [kGammaRemGSlab_of_mem I hx, Set.indicator_of_mem hx, kGammaRemG]
    · simp [kGammaRemGSlab_of_notMem I hx, Set.indicator_of_notMem hx]
  rw [e]
  exact hK.add hR

end Model

end RegularityStructures

end
