/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.SettingNear
public import RegularityStructures.Abstract.Singular.TwoModel.BoundsNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.TwoModel.GrowthCommonW
public import RegularityStructures.Abstract.Singular.TwoModel.RealisingG

/-!
# Window hypotheses for the difference model, near-pair `Γ`-bounds

The difference model satisfies `ExtSettingWNear`; for every `ε > 0` the scaling `λ > 0` can be
chosen with `C_{dΓ} ≤ λ G` and `λ ≤ C_{dΓ}/G + ε`, `G = max(C_{Γ₁}, C_{Γ₂}, 1)`, for models whose
`Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

namespace Model

variable {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {γ CPi₁ CPi₂ CGam₁ CGam₂ CdPi CdGam : ℝ}

/-- **The difference model satisfies the standing window hypotheses.** -/
theorem extSettingW_modelSum_near (hh : ShellProfile h N)
    (hreal₁ : M₁.IsRealisingP h γ P I V) (hreal₂ : M₂.IsRealisingP h γ P I V)
    (hI : IsAbstractIntegration P V I 2) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hPi₂ : M₂.PiBoundOn γ CPi₂ hairerTimeWindow) (hGam₁ : M₁.GammaNearOn γ CGam₁ hairerTimeWindow)
    (hGam₂ : M₂.GammaNearOn γ CGam₂ hairerTimeWindow)
    (hCPi₂ : 0 ≤ CPi₂) (hlam : 0 < lam) (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow)
    (hdGam : M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow)
    (h0 : 0 ≤ max (max CGam₁ CGam₂) (lam⁻¹ * CdGam))
    (g₁ : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₁.GrowthModel γ C' C'' ρP ρG p q)
    (g₂ : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₂.GrowthModel γ C' C'' ρP ρG p q)
    (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
      ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N')
    (hIp : ∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) (hNN : N' ≤ N) :
    (TwoModel.modelSum (lam := lam) hreal₁.poly hreal₂.poly).ExtSettingWNear h N γ
      (TwoModel.polySectorSum P) (TwoModel.intSum P I) (TwoModel.sectorSum P V)
      (max CPi₂ (lam⁻¹ * CdPi)) (max (max CGam₁ CGam₂) (lam⁻¹ * CdGam)) where
  profile := hh
  realising := by
    obtain ⟨C₁, C₁', C₂, C₂', ρP, ρG, p, q, G₁, G₂⟩ := TwoModel.exists_common_growthModel g₁ g₂
    exact TwoModel.isRealisingP_modelSum_growth (lam := lam) hh hreal₁.poly hreal₂.poly hV hVb
      G₁ G₂ hdeg hreal₁ hreal₂
  integration := TwoModel.isAbstractIntegration_intSum P hV hVb hI
  sector := TwoModel.isSector_sectorSum P hV hVb
  basis_mem a ha s hs := TwoModel.sectorSum_basis P hVb ha s hs
  deg_gtV s hs hlt := by
    rcases s with j | j
    · exact hdeg j.1 ((TwoModel.single_mem_sectorSum_iff P _).1 hs) hlt
    · exact hdeg j ((TwoModel.single_mem_sectorSum_iff P _).1 hs) hlt
  deg_gt4 s hlt := by
    rcases s with j | j
    · exact hdeg4 j.1 hlt
    · exact hdeg4 j hlt
  piBound := TwoModel.piBoundOn_modelSum hreal₁.poly hreal₂.poly hlam hPi₂ hdPi
  gammaBound := TwoModel.gammaBoundOn_modelSum_near hreal₁.poly hreal₂.poly hlam h0 hGam₁ hGam₂ hdGam
  piBound_nonneg := hCPi₂.trans (le_max_left _ _)
  growth := TwoModel.exists_growthModel_modelSum hreal₁.poly hreal₂.poly hlam g₁ g₂
  poly_largeV s hs hlt k hk := by
    rcases s with j | j
    · exact hN' j.1 ((TwoModel.single_mem_sectorSum_iff P _).1 hs) hlt k hk
    · exact hN' j ((TwoModel.single_mem_sectorSum_iff P _).1 hs) hlt k hk
  integration_poly a ha kk := TwoModel.intSum_apply_emb P hIp ha kk
  poly_le := hNN

/-- For every `ε > 0` there is `λ > 0` with `C_{dΓ} ≤ λ G` and `λ ≤ C_{dΓ}/G + ε`
(`G = max (max C_{Γ₁} C_{Γ₂}) 1`) for which the difference model satisfies `ExtSettingWNear`. -/
theorem exists_lam_extSettingW_near (hh : ShellProfile h N)
    (hreal₁ : M₁.IsRealisingP h γ P I V) (hreal₂ : M₂.IsRealisingP h γ P I V)
    (hI : IsAbstractIntegration P V I 2) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hPi₂ : M₂.PiBoundOn γ CPi₂ hairerTimeWindow) (hGam₁ : M₁.GammaNearOn γ CGam₁ hairerTimeWindow)
    (hGam₂ : M₂.GammaNearOn γ CGam₂ hairerTimeWindow)
    (hCPi₂ : 0 ≤ CPi₂) (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow)
    (hdGam : M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow) (hCdGam : 0 ≤ CdGam)
    (g₁ : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₁.GrowthModel γ C' C'' ρP ρG p q)
    (g₂ : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₂.GrowthModel γ C' C'' ρP ρG p q)
    (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
      ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N')
    (hIp : ∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) (hNN : N' ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ CdGam / max (max CGam₁ CGam₂) 1 + ε ∧
      CdGam ≤ lam * max (max CGam₁ CGam₂) 1 ∧
      (TwoModel.modelSum (lam := lam) hreal₁.poly hreal₂.poly).ExtSettingWNear h N γ
        (TwoModel.polySectorSum P) (TwoModel.intSum P I) (TwoModel.sectorSum P V)
        (max CPi₂ (lam⁻¹ * CdPi)) (max (max (max CGam₁ 1) (max CGam₂ 1)) (lam⁻¹ * CdGam)) := by
  set G : ℝ := max (max CGam₁ CGam₂) 1 with hG
  have hG1 : 1 ≤ G := le_max_right _ _
  have hG0 : 0 < G := lt_of_lt_of_le one_pos hG1
  set lam : ℝ := max (CdGam / G) ε with hlam
  have hlam0 : 0 < lam := lt_of_lt_of_le hε (le_max_right _ _)
  have hlamG : CdGam ≤ lam * G := by
    have : CdGam / G ≤ lam := le_max_left _ _
    rwa [div_le_iff₀ hG0] at this
  refine ⟨lam, hlam0, ?_, hlamG, ?_⟩
  · exact max_le (le_add_of_nonneg_right hε.le) (le_add_of_nonneg_left (div_nonneg hCdGam hG0.le))
  · have hG₁ : M₁.GammaNearOn γ (max CGam₁ 1) hairerTimeWindow :=
      hGam₁.mono M₁ (le_max_left _ _)
    have hG₂ : M₂.GammaNearOn γ (max CGam₂ 1) hairerTimeWindow :=
      hGam₂.mono M₂ (le_max_left _ _)
    exact extSettingW_modelSum_near hh hreal₁ hreal₂ hI hV hVb hdeg hdeg4 hPi₂ hG₁ hG₂ hCPi₂ hlam0 hdPi
      hdGam
      (le_trans (zero_le_one.trans (le_max_right _ _))
        (le_trans (le_max_right _ _) (le_max_left _ _))) g₁ g₂ hN' hIp hNN

end Model

end RegularityStructures

end
