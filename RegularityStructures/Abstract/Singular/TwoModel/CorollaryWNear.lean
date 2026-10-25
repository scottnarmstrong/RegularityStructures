/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.TwoModel.Theorem71WNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Singular.TwoModel.Corollary
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# The two-model Theorem 7.1 with a prescribed size of the model difference, near-pair `Γ`-bounds

`exists_singularDiffBoundOn_kGammaRemG_of_le_win_near`: the weighted two-model Theorem 7.1 for
`𝒦_γ + R_γ` and a kernel pair, when the constants `CdPi`, `CdGam`, `CdGam2` of the model difference
are bounded by `δ > 0`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Model

/-- **Two-model Theorem 7.1 (weighted) with the model-difference size `δ`**: the constants
`CdPi`, `CdGam`, `CdGam2` of the model difference are bounded by `δ > 0`. -/
theorem exists_singularDiffBoundOn_kGammaRemG_of_le_win_near {𝒯 : RegularityStructure ι}
    (γ η α : ℝ) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N') {h r : ParabolicSpace → ℝ}
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
      (T C₁ C₂ Cd CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam CdGam2 CI CΓ2₁ CΓ2₂ δ : ℝ)
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), 0 < δ → CdPi ≤ δ → CdGam ≤ δ →
      CdGam2 ≤ δ →
      LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T →
      LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T →
      M₁.IsRealisingP h γ P I V →
      M₂.IsRealisingP h γ P I V → IsAbstractIntegration P V I 2 →
      (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) →
      (∀ i j, |I (Pi.single i 1) j| ≤ CI) → 0 ≤ CI → 0 ≤ Cd → (∀ z, f₁ z ∈ V) → (∀ z, f₂ z ∈ V) →
      M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow →
      M₁.GammaNearOn (γ + 2) CΓ2₁ (timeSlab T) → M₂.GammaNearOn (γ + 2) CΓ2₂ (timeSlab T) →
      M₁.GammaDiffNearOn M₂ (γ + 2) CdGam2 (timeSlab T) →
      M₁.SingularDiffBoundOn M₂ timeZeroDist γ η Cd (timeSlab T) f₁ f₂ →
      M₁.SingularDiffBoundOn M₂ timeZeroDist (γ + 2) (min α η + 2)
        (C * ((max 1 (max CGam₁ CGam₂) * max CPi₂ 1 +
          Fintype.card (TwoModel.NonPoly P ⊕ ι) * CI) * max 1 (max CΓ2₁ CΓ2₂)) *
          (δ * C₁ + Cd)) (timeSlab T)
        (M₁.kGammaRemG h r P I γ f₁) (M₂.kGammaRemG h r P I γ f₂) ∧
      (∀ x ∈ timeSlab T, ∀ i, 𝒯.deg i < γ + 2 →
        |M₁.kGammaRemG h r P I γ f₁ x i - M₂.kGammaRemG h r P I γ f₂ x i| ≤
          C * ((max 1 (max CGam₁ CGam₂) * max CPi₂ 1 +
            Fintype.card (TwoModel.NonPoly P ⊕ ι) * CI) * max 1 (max CΓ2₁ CΓ2₂)) *
            (δ * C₁ + Cd) * singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg i)) := by
  obtain ⟨C, hC0, hC⟩ := exists_singularDiffBoundOn_kGammaRemG_win_near γ η α N P hp hγ hdeg hαγ hαη
    hN hNγ hnat hni hV hVb hVα
  refine ⟨C, hC0, ?_⟩
  intro M₁ M₂ f₁ f₂ T C₁ C₂ Cd CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam CdGam2 CI CΓ2₁ CΓ2₂ lam I
    hl0 h1 h2 h3 S₁ S₂ hr₁ hr₂ hI hIp hCI hCI0 hCd hf₁ hf₂ hdP hdG hG₁ hG₂ hdG2 hfd
  obtain ⟨hmain, hpt⟩ := hC M₁ M₂ f₁ f₂ T C₁ C₂ Cd CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam CdGam2 CI CΓ2₁
    CΓ2₂ lam I hl0 S₁ S₂ hr₁ hr₂ hI hIp hCI hf₁ hf₂ hdP hdG hG₁ hG₂ hdG2 hfd
  have hn : (0 : ℝ) ≤ Fintype.card (TwoModel.NonPoly P ⊕ ι) * CI :=
    mul_nonneg (Nat.cast_nonneg _) hCI0
  have hG := TwoModel.max_one_gamConstSum_le (a := CGam₁) (b := CGam₂) hl0 h2
  have hΓ := TwoModel.max_one_gamConstSum_le (a := CΓ2₁) (b := CΓ2₂) hl0 h3
  have hP := TwoModel.piConstSum_le (CPi := CPi₂) hl0 h1
  have hP0 : 0 ≤ TwoModel.piConstSum lam CPi₂ CdPi := S₂.hCPi.trans (le_max_left _ _)
  have hK : TwoModel.thm71SumConst lam CPi₂ CdPi CGam₁ CGam₂ CdGam CΓ2₁ CΓ2₂ CdGam2 CI
        (Fintype.card (TwoModel.NonPoly P ⊕ ι)) ≤
      (max 1 (max CGam₁ CGam₂) * max CPi₂ 1 +
        Fintype.card (TwoModel.NonPoly P ⊕ ι) * CI) * max 1 (max CΓ2₁ CΓ2₂) := by
    unfold TwoModel.thm71SumConst
    have a0 : 0 ≤ max 1 (TwoModel.gamConstSum lam CGam₁ CGam₂ CdGam) :=
      zero_le_one.trans (le_max_left _ _)
    have hA : max 1 (TwoModel.gamConstSum lam CGam₁ CGam₂ CdGam) *
        TwoModel.piConstSum lam CPi₂ CdPi ≤ max 1 (max CGam₁ CGam₂) * max CPi₂ 1 :=
      mul_le_mul hG hP hP0 (zero_le_one.trans (le_max_left _ _))
    refine mul_le_mul (add_le_add hA le_rfl) hΓ
      (zero_le_one.trans (le_max_left _ _)) ?_
    exact add_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (zero_le_one.trans (le_max_right _ _))) hn
  have hlC : 0 ≤ lam * C₁ := mul_nonneg hl0.le S₁.hCf
  have hmax : max (lam * C₁) Cd ≤ lam * C₁ + Cd := max_le (by linarith) (by linarith)
  have hKn : 0 ≤ TwoModel.thm71SumConst lam CPi₂ CdPi CGam₁ CGam₂ CdGam CΓ2₁ CΓ2₂ CdGam2 CI
        (Fintype.card (TwoModel.NonPoly P ⊕ ι)) := by
    unfold TwoModel.thm71SumConst
    exact mul_nonneg (add_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hP0) hn)
      (zero_le_one.trans (le_max_left _ _))
  have hle : C * TwoModel.thm71SumConst lam CPi₂ CdPi CGam₁ CGam₂ CdGam CΓ2₁ CΓ2₂ CdGam2 CI
        (Fintype.card (TwoModel.NonPoly P ⊕ ι)) * max (lam * C₁) Cd ≤
      C * ((max 1 (max CGam₁ CGam₂) * max CPi₂ 1 +
        Fintype.card (TwoModel.NonPoly P ⊕ ι) * CI) * max 1 (max CΓ2₁ CΓ2₂)) *
        (lam * C₁ + Cd) :=
    (mul_le_mul_of_nonneg_left hmax (mul_nonneg hC0 hKn)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC0) (add_nonneg hlC hCd))
  refine ⟨hmain.mono hle, fun x hx i hi => (hpt x hx i hi).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (Layer.singularWeight_nonneg x) _)

end Model

end RegularityStructures

end
