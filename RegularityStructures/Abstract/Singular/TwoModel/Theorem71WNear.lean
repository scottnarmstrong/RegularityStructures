/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Theorem71.MainWNear
public import RegularityStructures.Abstract.Singular.TwoModel.IdentWNear
public import RegularityStructures.Abstract.Singular.TwoModel.LayerSumNear
public import RegularityStructures.Abstract.Singular.TwoModel.LayerSumWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Singular.TwoModel.GrowthCommonW
public import RegularityStructures.Abstract.Singular.TwoModel.RealisingG
public import RegularityStructures.Abstract.Singular.TwoModel.Theorem71
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# Hairer's Theorem 7.1, two-model half, near-pair `Γ`-bounds

The local Lipschitz bound for `𝒦_γ + R_γ` in the model and in `f`
(`exists_singularDiffBoundOn_kGammaRemG_win_near`): the model bounds are those of
`LayerSettingWNear` (on `hairerTimeWindow`, with qualitative growth), the difference bounds are
`PiDiffBoundOn` and `GammaDiffNearOn` on `hairerTimeWindow`, and the kernel is a kernel pair
`(h, r)`. The proof applies the single-model bound `exists_singularBoundOn_kGammaRemG_win_near` to
the difference model.

This is the version for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Model

/-- **Hairer's Theorem 7.1, two-model half, window** (local Lipschitz bound for `𝒦_γ + R_γ`). -/
theorem exists_singularDiffBoundOn_kGammaRemG_win_near {𝒯 : RegularityStructure ι} (γ η α : ℝ)
    (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N') {h r : ParabolicSpace → ℝ}
    (hp : KernelPair h r N) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hαγ : α ≤ γ) (hαη : -2 < min α η)
    (hN : N' ≤ N) (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N')
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    {V : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hVα : ∀ i, (Pi.single i 1 : ι → ℝ) ∈ V → α ≤ 𝒯.deg i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M₁ M₂ : Model 𝒯 parabolicSemigroup) (f₁ f₂ : ParabolicSpace → ι → ℝ)
      (T C₁ C₂ Cd CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam CdGam2 CI CΓ2₁ CΓ2₂ lam : ℝ)
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), 0 < lam →
      LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T →
      LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T →
      M₁.IsRealisingP h γ P I V →
      M₂.IsRealisingP h γ P I V → IsAbstractIntegration P V I 2 →
      (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) →
      (∀ i j, |I (Pi.single i 1) j| ≤ CI) → (∀ z, f₁ z ∈ V) → (∀ z, f₂ z ∈ V) →
      M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow →
      M₁.GammaNearOn (γ + 2) CΓ2₁ (timeSlab T) → M₂.GammaNearOn (γ + 2) CΓ2₂ (timeSlab T) →
      M₁.GammaDiffNearOn M₂ (γ + 2) CdGam2 (timeSlab T) →
      M₁.SingularDiffBoundOn M₂ timeZeroDist γ η Cd (timeSlab T) f₁ f₂ →
      M₁.SingularDiffBoundOn M₂ timeZeroDist (γ + 2) (min α η + 2)
        (C * TwoModel.thm71SumConst lam CPi₂ CdPi CGam₁ CGam₂ CdGam CΓ2₁ CΓ2₂ CdGam2 CI
          (Fintype.card (TwoModel.NonPoly P ⊕ ι)) * max (lam * C₁) Cd) (timeSlab T)
        (M₁.kGammaRemG h r P I γ f₁) (M₂.kGammaRemG h r P I γ f₂) ∧
      (∀ x ∈ timeSlab T, ∀ i, 𝒯.deg i < γ + 2 →
        |M₁.kGammaRemG h r P I γ f₁ x i - M₂.kGammaRemG h r P I γ f₂ x i| ≤
          C * TwoModel.thm71SumConst lam CPi₂ CdPi CGam₁ CGam₂ CdGam CΓ2₁ CΓ2₂ CdGam2 CI
            (Fintype.card (TwoModel.NonPoly P ⊕ ι)) * max (lam * C₁) Cd *
            singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg i)) := by
  classical
  have hdeg' : ∀ j, (TwoModel.structSumU P).deg j < γ → -4 < (TwoModel.structSumU P).deg j := by
    intro j hj
    rcases j with i | i
    · exact hdeg i.1 hj
    · exact hdeg i hj
  have hni' : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range (TwoModel.polySectorSum P).emb → α ≤ (TwoModel.structSumU P).deg i →
        (TwoModel.structSumU P).deg i < γ →
        (multiDeg k : ℝ) ≠ (TwoModel.structSumU P).deg i + 2 := by
    intro k hk i hi h1 h2
    rcases i with i | i
    · exact hni k hk i.1 i.2 h1 h2
    · exact hni k hk i (fun ⟨kk, hkk⟩ => hi ⟨kk, by simp [TwoModel.polySectorSum, hkk]⟩) h1 h2
  obtain ⟨C, hC0, hC⟩ := exists_singularBoundOn_kGammaRemG_win_near (𝒯 := TwoModel.structSumU P) γ η α
    N (TwoModel.polySectorSum P) hp hγ hdeg' hαγ hαη hN hNγ hnat hni'
    (TwoModel.isSector_sectorSum P hV hVb) (fun a ha s hs => TwoModel.sectorSum_basis P hVb ha s hs)
    (TwoModel.le_deg_of_single_mem_sectorSum P hVα)
  refine ⟨C, hC0, ?_⟩
  intro M₁ M₂ f₁ f₂ T C₁ C₂ Cd CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam CdGam2 CI CΓ2₁ CΓ2₂ lam I
    hlam S₁ S₂ hr₁ hr₂ hI hIp hCI hf₁ hf₂ hdP hdG hG₁ hG₂ hdG2 hfd
  obtain ⟨_, _, _, _, _, _, _, _, G₁, G₂⟩ := TwoModel.exists_common_growthModel S₁.hgrowth S₂.hgrowth
  have h₁ := hr₁.poly
  have h₂ := hr₂.poly
  have hdeg2 : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j :=
    fun j hj _ => by linarith [hVα j hj, min_le_left α η]
  have hreal := TwoModel.isRealisingP_modelSum_growth (lam := lam) hp.shell h₁ h₂ hV hVb G₁ G₂
    hdeg2 hr₁ hr₂
  have hS := TwoModel.layerSettingW_modelSum_near h₁ h₂ hlam S₁ S₂ hdP hdG hfd
  have hΓ2 := TwoModel.gammaBoundOn_modelSum_const_near h₁ h₂ hlam hG₁ hG₂ hdG2
  have hint := TwoModel.isAbstractIntegration_intSum P hV hVb hI
  have hIp' : ∀ a ∈ TwoModel.sectorSum P V, ∀ kk : PolyIndex N',
      TwoModel.intSum P I a ((TwoModel.polySectorSum P).emb kk) = 0 :=
    fun a ha kk => TwoModel.intSum_apply_emb P hIp ha kk
  have hfV : ∀ z, TwoModel.liftSum P lam f₁ f₂ z ∈ TwoModel.sectorSum P V :=
    fun z => TwoModel.liftVec_mem_sectorSum P lam hVb (hf₁ z) (hf₂ z)
  obtain ⟨-, hB, hpt⟩ := hC (TwoModel.modelSum (lam := lam) h₁ h₂) (TwoModel.liftSum P lam f₁ f₂)
    T (max (lam * C₁) Cd) (TwoModel.piConstSum lam CPi₂ CdPi)
    (TwoModel.gamConstSum lam CGam₁ CGam₂ CdGam) CI
    (TwoModel.gamConstSum lam CΓ2₁ CΓ2₂ CdGam2) (TwoModel.intSum P I) hS hreal hint hIp'
    (TwoModel.abs_intSum_single_le P hCI) hfV hΓ2
  have hx' : ∀ x ∈ timeSlab T, ∀ i : ι,
      TwoModel.rightPart P ((TwoModel.modelSum (lam := lam) h₁ h₂).kGammaRemG h r
        (TwoModel.polySectorSum P) (TwoModel.intSum P I) γ (TwoModel.liftSum P lam f₁ f₂) x) i =
      M₁.kGammaRemG h r P I γ f₁ x i - M₂.kGammaRemG h r P I γ f₂ x i := by
    intro x hx i
    have := (TwoModel.kGammaRemG_modelSum_parts_win_near (N := N) hp hlam.ne' h₁ h₂ hV hVb hI S₁ S₂
      hN hni hf₁ hx).2
    exact congrFun this i
  have hinc : ∀ x ∈ timeSlab T, ∀ y ∈ timeSlab T, ∀ j : ι,
      ((TwoModel.modelSum (lam := lam) h₁ h₂).kGammaRemG h r (TwoModel.polySectorSum P)
          (TwoModel.intSum P I) γ (TwoModel.liftSum P lam f₁ f₂) y -
        (TwoModel.modelSum (lam := lam) h₁ h₂).gammaMap y x
          ((TwoModel.modelSum (lam := lam) h₁ h₂).kGammaRemG h r (TwoModel.polySectorSum P)
            (TwoModel.intSum P I) γ (TwoModel.liftSum P lam f₁ f₂) x)) (Sum.inr j) =
      (M₁.kGammaRemG h r P I γ f₁ y - M₁.gammaMap y x (M₁.kGammaRemG h r P I γ f₁ x) -
        (M₂.kGammaRemG h r P I γ f₂ y - M₂.gammaMap y x (M₂.kGammaRemG h r P I γ f₂ x))) j := by
    intro x hx y hy j
    have := TwoModel.rightPart_sub_gammaSum_kGammaRemG_win_near (N := N) hp hlam.ne' h₁ h₂ hV hVb hI
      S₁ S₂ hN hni hf₁ hx hy
    exact congrFun this j
  refine ⟨⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩, fun x hx i hi => ?_⟩
  · have := hB.1 x hx hρ (Sum.inr i) hi
    have e := hx' x hx i
    refine le_of_eq_of_le ?_ this
    · rw [← e]; rfl
  · have := hB.2 x hx y hy hρx hρy hd (Sum.inr j) hj
    refine le_of_eq_of_le ?_ this
    exact congrArg abs (by simpa only [Pi.sub_apply] using (hinc x hx y hy j).symm)
  · have := hpt x hx (Sum.inr i) hi
    refine le_of_eq_of_le ?_ this
    rw [← hx' x hx i]; rfl

end Model

end RegularityStructures

end
