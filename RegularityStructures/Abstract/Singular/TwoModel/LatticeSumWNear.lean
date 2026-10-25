/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.MeasReconWNear
public import RegularityStructures.Abstract.Singular.KGamma.SupMainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.PairingWNear
public import RegularityStructures.Abstract.Singular.TwoModel.LayerSumWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.Kernel.Shell
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Pairing
public import RegularityStructures.Abstract.Singular.Remainder.Linear
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG
public import RegularityStructures.Abstract.Singular.TwoModel.LatticeSum

/-!
# Reconstruction and pairings of the lift `f⊕` are differences, near-pair `Γ`-bounds

For two models, their sum model and the lift `f⊕ = liftSum P λ f₁ f₂`, the following quantities for
`f⊕` are the differences of those for `(M₁, f₁)` and `(M₂, f₂)`:

* the model pairings, lattice approximations and reconstructions
  (`pairing_regPi_modelSum_liftSum_win_near`, `latticeApprox_modelSum_liftSum_win_near`,
  `latticeRecon_modelSum_liftSum_win_near`);
* the shell pairings and the coefficients of `𝒦_γ` (`singShellPairing_modelSum_win_near`,
  `nCoeffS_modelSum_win_near`, `nVecS_modelSum_parts_win_near`);
* the remainder terms (`remPairing_modelSum_win_near`, `remVecG_modelSum_parts_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Filter MeasureTheory Set

open scoped ContDiff Topology

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {f₁ f₂ : ParabolicSpace → ι → ℝ} {γ η α C₁ C₂ CPi₁ CPi₂ CGam₁ CGam₂ T : ℝ}

theorem pairing_regPi_modelSum_liftSum_win_near (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) (hlam : lam ≠ 0)
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T) {g : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R A : ℝ} (hg : IsScaledTest g x R A) :
    parabolicSemigroup.pairing ((modelSum (lam := lam) h₁ h₂).regPi x (liftSum P lam f₁ f₂ x)) g =
      parabolicSemigroup.pairing (M₁.regPi x (f₁ x)) g -
        parabolicSemigroup.pairing (M₂.regPi x (f₂ x)) g := by
  obtain ⟨_, _, _, _, _, _, G₁⟩ := S₁.hgrowth
  obtain ⟨_, _, _, _, _, _, G₂⟩ := S₂.hgrowth
  rw [regPi_modelSum_liftSum h₁ h₂ hlam]
  exact pairing_sub_of_tendsto parabolicSemigroup
    (fun s hs => Model.integrable_regPi_mul_of_scaled_growth G₁ (S₁.hfT x) hg hs.1 hs.2)
    (fun s hs => Model.integrable_regPi_mul_of_scaled_growth G₂ (S₂.hfT x) hg hs.1 hs.2)
    (Model.tendsto_integral_regPi_mul_of_scaled_growth G₁ S₁.hdeg (S₁.hfT x) hg)
    (Model.tendsto_integral_regPi_mul_of_scaled_growth G₂ S₂.hdeg (S₂.hfT x) hg)

theorem latticeApprox_modelSum_liftSum_win_near (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) (hlam : lam ≠ 0)
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T) {ψ : ParabolicSpace → ℝ}
    {x₀ : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x₀) → ψ w = 0) {n : ℕ} (hn : 3 ≤ n) :
    (modelSum (lam := lam) h₁ h₂).latticeApprox (liftSum P lam f₁ f₂) ψ n =
      M₁.latticeApprox f₁ ψ n - M₂.latticeApprox f₂ ψ n := by
  obtain ⟨s, hs'⟩ := Model.exists_finset_support_mul_latticeCell hs n
  rw [Model.latticeApprox_eq_sum _ hs', Model.latticeApprox_eq_sum _ hs',
    Model.latticeApprox_eq_sum _ hs', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨A, hA⟩ := exists_isScaledTest_of_latticeCell
    (hψ.mul (contDiff_latticeCell n k)) hn fun w h => right_ne_zero_of_mul h
  exact pairing_regPi_modelSum_liftSum_win_near h₁ h₂ hlam S₁ S₂ hA

theorem latticeRecon_modelSum_liftSum_win_near (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) (hlam : lam ≠ 0)
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T) {ψ : ParabolicSpace → ℝ}
    {x₀ : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x₀) → ψ w = 0) {L₁ L₂ : ℝ}
    (t₁ : Tendsto (M₁.latticeApprox f₁ ψ) atTop (𝓝 L₁))
    (t₂ : Tendsto (M₂.latticeApprox f₂ ψ) atTop (𝓝 L₂)) :
    Tendsto ((modelSum (lam := lam) h₁ h₂).latticeApprox (liftSum P lam f₁ f₂) ψ) atTop
        (𝓝 (L₁ - L₂)) ∧
      (modelSum (lam := lam) h₁ h₂).latticeRecon (liftSum P lam f₁ f₂) ψ = L₁ - L₂ := by
  have t : Tendsto ((modelSum (lam := lam) h₁ h₂).latticeApprox (liftSum P lam f₁ f₂) ψ) atTop
      (𝓝 (L₁ - L₂)) := by
    refine (t₁.sub t₂).congr' ?_
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (latticeApprox_modelSum_liftSum_win_near h₁ h₂ hlam S₁ S₂ hψ hs hn).symm
  exact ⟨t, t.limUnder_eq⟩

variable {h : ParabolicSpace → ℝ} {N : ℕ}

theorem singShellPairing_modelSum_win_near (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) (hh : ShellProfile h N) (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T) (k : Fin 4 →₀ ℕ) (n : ℕ)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    (modelSum (lam := lam) h₁ h₂).singShellPairing h (liftSum P lam f₁ f₂) x k n =
      M₁.singShellPairing h f₁ x k n - M₂.singShellPairing h f₂ x k n := by
  obtain ⟨C, -, hC⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  have hg := hC n x
  have t₁ := Model.tendsto_latticeApprox_lineIter_scaledShell_win_near hh hc S₁ k n hx.2
  have t₂ := Model.tendsto_latticeApprox_lineIter_scaledShell_win_near hh hc S₂ k n hx.2
  obtain ⟨-, hrec⟩ := latticeRecon_modelSum_liftSum_win_near h₁ h₂ hlam S₁ S₂ hg.contDiff hg.supp
    t₁ t₂
  unfold Model.singShellPairing
  rw [hrec, pairing_regPi_modelSum_liftSum_win_near h₁ h₂ hlam S₁ S₂ hg]
  ring

theorem nCoeffS_modelSum_win_near (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) (hh : ShellProfile h N) (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T) (k : Fin 4 →₀ ℕ)
    (hkγ : (multiDeg k : ℝ) < γ + 2) (hN : N' ≤ N)
    (hni : ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    (modelSum (lam := lam) h₁ h₂).nCoeffS h (liftSum P lam f₁ f₂) x k =
      M₁.nCoeffS h f₁ x k - M₂.nCoeffS h f₂ x k := by
  have s₁ := Model.summable_singShellPairing_win_near 𝒯 γ η α S₁.hdeg S₁.hγ S₁.hαγ S₁.hαη
    hh hc k hkγ P hN hni M₁ f₁ T C₁ CPi₁ CGam₁ S₁ h₁ hx
  have s₂ := Model.summable_singShellPairing_win_near 𝒯 γ η α S₁.hdeg S₁.hγ S₁.hαγ S₁.hαη
    hh hc k hkγ P hN hni M₂ f₂ T C₂ CPi₂ CGam₂ S₂ h₂ hx
  unfold Model.nCoeffS
  rw [← s₁.tsum_sub s₂]
  exact tsum_congr fun n => singShellPairing_modelSum_win_near h₁ h₂ hlam hh hc S₁ S₂ k n hx

theorem nVecS_modelSum_parts_win_near (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) (hh : ShellProfile h N) (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0)
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T) (hN : N' ≤ N)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    leftPart P ((modelSum (lam := lam) h₁ h₂).nVecS h (polySectorSum P) γ
        (liftSum P lam f₁ f₂) x) = 0 ∧
      rightPart P ((modelSum (lam := lam) h₁ h₂).nVecS h (polySectorSum P) γ
        (liftSum P lam f₁ f₂) x) = M₁.nVecS h P γ f₁ x - M₂.nVecS h P γ f₂ x := by
  classical
  unfold Model.nVecS
  refine ⟨?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun kk _ => ?_
    split_ifs
    · change leftPart P (_ • Pi.single (Sum.inr (P.emb kk)) 1) = 0
      rw [map_smul, leftPart_single_inr, smul_zero]
    · exact map_zero _
  · rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun kk _ => ?_
    by_cases hk : polyDeg N' kk < γ + 2
    · simp only [hk, ite_true]
      have hk' : (multiDeg kk.1 : ℝ) < γ + 2 := hk
      change rightPart P (_ • Pi.single (Sum.inr (P.emb kk)) 1) = _
      rw [map_smul, rightPart_single_inr,
        nCoeffS_modelSum_win_near h₁ h₂ hlam hh hc S₁ S₂ kk.1 hk' hN (hni kk.1 hk') hx, sub_div,
        sub_smul]
    · simp [hk]

private theorem cell_supp_win (ψ : ParabolicSpace → ℝ) (j : LatticeIndex) (w : ParabolicSpace)
    (hw : 1 < parabolicNorm (w - latticePoint 3 j)) : ψ w * latticeCell 3 j w = 0 := by
  rw [latticeCell_eq_zero_of_one_lt hw, mul_zero]

theorem remPairing_modelSum_win_near (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T)     {r : ParabolicSpace → ℝ} (hr : RemKernel r) (k : Fin 4 →₀ ℕ)
    {z : ParabolicSpace} (hz : z.1 ≤ T) :
    (modelSum (lam := lam) h₁ h₂).remPairing (liftSum P lam f₁ f₂)
        (fun y => lineIter (multiDirs k) r (z - y)) =
      M₁.remPairing f₁ (fun y => lineIter (multiDirs k) r (z - y)) -
        M₂.remPairing f₂ (fun y => lineIter (multiDirs k) r (z - y)) := by
  set ψ : ParabolicSpace → ℝ := fun y => lineIter (multiDirs k) r (z - y) with hψ
  have r₁ := S₁.remSumm_lineIter_win hr k hz
  have r₂ := S₂.remSumm_lineIter_win hr k hz
  have hcell : ∀ j : LatticeIndex,
      (modelSum (lam := lam) h₁ h₂).latticeRecon (liftSum P lam f₁ f₂)
          (fun y => ψ y * latticeCell 3 j y) =
        M₁.latticeRecon f₁ (fun y => ψ y * latticeCell 3 j y) -
          M₂.latticeRecon f₂ (fun y => ψ y * latticeCell 3 j y) := fun j =>
    (latticeRecon_modelSum_liftSum_win_near h₁ h₂ hlam S₁ S₂
      (r₁.contDiff.mul (contDiff_latticeCell 3 j)) (cell_supp_win ψ j)
      (r₁.tendsto j) (r₂.tendsto j)).2
  unfold Model.remPairing
  simp only [hcell]
  exact r₁.summable.tsum_sub r₂.summable

theorem remVecG_modelSum_parts_win_near (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    (hlam : lam ≠ 0) (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T)     {r : ParabolicSpace → ℝ} (hr : RemKernel r) {x : ParabolicSpace} (hx : x.1 ≤ T) :
    leftPart P ((modelSum (lam := lam) h₁ h₂).remVecG r (polySectorSum P) γ
        (liftSum P lam f₁ f₂) x) = 0 ∧
      rightPart P ((modelSum (lam := lam) h₁ h₂).remVecG r (polySectorSum P) γ
        (liftSum P lam f₁ f₂) x) = M₁.remVecG r P γ f₁ x - M₂.remVecG r P γ f₂ x := by
  classical
  unfold Model.remVecG
  refine ⟨?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun kk _ => ?_
    split_ifs
    · change leftPart P (_ • Pi.single (Sum.inr (P.emb kk)) 1) = 0
      rw [map_smul, leftPart_single_inr, smul_zero]
    · exact map_zero _
  · rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun kk _ => ?_
    by_cases hk : polyDeg N' kk < γ + 2
    · simp only [hk, ite_true]
      change rightPart P (_ • Pi.single (Sum.inr (P.emb kk)) 1) = _
      rw [map_smul, rightPart_single_inr,
        remPairing_modelSum_win_near h₁ h₂ hlam S₁ S₂ hr kk.1 hx, sub_div, sub_smul]
    · simp [hk]

end TwoModel

end RegularityStructures

end
