/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.GammaNear
public import RegularityStructures.Abstract.Ext514W.TwoModelSettingNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Ext514.TwoModelGamma
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising

/-!
# The two-model bound for `Γ` on the integrated symbols `I e_i`, near-pair `Γ`-bounds

[Hai14, (5.18)], second line, `Γ` part: for two models `M₁, M₂` realising the kernel with profile
`h` for `I` on `V`, with window bounds and window difference bounds at level `γ` (and qualitative
growth models), `e_i ∈ V`, `deg i < γ`, `x, y` in the time slab `(0, 1]` with
`d = d(y, x) ≤ gammaNearRadius` and `deg j < deg i + 2`,
`|((Γ¹_{yx} − Γ²_{yx}) I e_i)_j| ≤ c (C_{dΠ} G² + C_{dΓ} (C_I + C_{Π₂} G)) d^{deg i + 2 − deg j}`,
`G = max (max C_{Γ₁} C_{Γ₂}) 1` (`exists_abs_gammaMap_integral_sub_le_win_near`).

This is the version for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

namespace Model

variable {P : PolynomialSector 𝒯 N'}

/-- **Two-model bound for `Γ` on `I e_i`, window version** [Hai14, (5.18)]. -/
theorem exists_abs_gammaMap_integral_sub_le_win_near (hh : ShellProfile h N) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) {γ : ℝ}
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (P : PolynomialSector 𝒯 N') {i : ι} (hi : 𝒯.deg i < γ)
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V)
    (hnat1 : ∀ k : PolyIndex N', polyDeg N' k < 𝒯.deg i + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ 𝒯.deg i + 2 - multiDeg k.1)
    (hnat2 : ∀ k : PolyIndex N', polyDeg N' k < 𝒯.deg i + 2 →
      ∀ j, j ∉ Set.range P.emb → (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j ≤ 𝒯.deg i →
        (multiDeg k.1 : ℝ) ≠ 𝒯.deg j + 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M₁ M₂ : Model 𝒯 parabolicSemigroup)
      {CPi₂ CGam₁ CGam₂ CdPi CdGam CI : ℝ} (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)),
      M₁.IsRealisingP h γ P I V → M₂.IsRealisingP h γ P I V → IsAbstractIntegration P V I 2 →
      M₁.GammaNearOn γ CGam₁ hairerTimeWindow →
      M₂.PiBoundOn γ CPi₂ hairerTimeWindow → M₂.GammaNearOn γ CGam₂ hairerTimeWindow →
      0 ≤ CPi₂ →
      M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow →
      0 ≤ CdPi → 0 ≤ CdGam → (∀ a b, |I (Pi.single a 1) b| ≤ CI) →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₁.GrowthModel γ C' C'' ρP ρG p q) →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₂.GrowthModel γ C' C'' ρP ρG p q) →
      (∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
        ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N') →
      (∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0) → N' ≤ N →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius →
      ∀ (j : ι), 𝒯.deg j < 𝒯.deg i + 2 →
      |M₁.gammaMap y x (I (Pi.single i 1)) j - M₂.gammaMap y x (I (Pi.single i 1)) j| ≤
        c * (CdPi * max (max CGam₁ CGam₂) 1 * max (max CGam₁ CGam₂) 1 +
          CdGam * (CI + CPi₂ * max (max CGam₁ CGam₂) 1)) *
          parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j) := by
  classical
  by_cases hip : i ∈ Set.range P.emb
  · refine ⟨0, le_rfl, ?_⟩
    intro M₁ M₂ CPi₂ CGam₁ CGam₂ CdPi CdGam CI I _ _ hI _ _ _ _ _ _ _ _ _ _ _ _ _ x y _ _ _ j _
    rw [integral_single_eq_zero_of_mem_range hI hVi hip]
    simp
  · have hdeg4' : ∀ s : TwoModel.NonPoly P ⊕ ι,
        (TwoModel.structSumU P).deg s < γ → -4 < (TwoModel.structSumU P).deg s := by
      intro s hlt
      rcases s with j | j
      · exact hdeg4 j.1 hlt
      · exact hdeg4 j hlt
    have hVi' : (Pi.single (Sum.inl ⟨i, hip⟩) 1 : TwoModel.NonPoly P ⊕ ι → ℝ) ∈
        TwoModel.sectorSum P V := (TwoModel.single_mem_sectorSum_iff P _).2 hVi
    obtain ⟨c, hc0, hc⟩ := exists_abs_gammaMap_integral_le_win_near (𝒯 := TwoModel.structSumU P)
      (V := TwoModel.sectorSum P V) (N' := N') hh hdeg4'
      (TwoModel.polySectorSum P) (i := Sum.inl ⟨i, hip⟩) hi hVi' hnat1
      (by
        intro k hk s hs hsV hsle
        rcases s with j | j
        · exact hnat2 k hk j.1 j.2 ((TwoModel.single_mem_sectorSum_iff P _).1 hsV) hsle
        · refine hnat2 k hk j ?_ ((TwoModel.single_mem_sectorSum_iff P _).1 hsV) hsle
          intro hr
          obtain ⟨l, rfl⟩ := hr
          exact hs ⟨l, rfl⟩)
    refine ⟨c, hc0, ?_⟩
    intro M₁ M₂ CPi₂ CGam₁ CGam₂ CdPi CdGam CI I hr₁ hr₂ hI hGam₁ hPi₂ hGam₂
      hCPi₂ hdPi hdGam hCdPi hCdGam hCI g₁ g₂ hN' hIp hNN x y hx hy hxy j hj
    set G : ℝ := max (max CGam₁ CGam₂) 1 with hG
    have hG1 : 1 ≤ G := le_max_right _ _
    have hG0 : 0 < G := lt_of_lt_of_le one_pos hG1
    set T : ℝ := parabolicNorm (y - x) ^ (𝒯.deg i + 2 - 𝒯.deg j) with hT
    have hT0 : 0 ≤ T := Real.rpow_nonneg (parabolicNorm_nonneg _) _
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI i i)
    refine le_of_forall_pos_le_add_mul (B := c * (CI * G + CPi₂ * G * G) * T)
      (mul_nonneg (mul_nonneg hc0 (add_nonneg (mul_nonneg hCI0 hG0.le)
        (mul_nonneg (mul_nonneg hCPi₂ hG0.le) hG0.le))) hT0) fun ε hε => ?_
    obtain ⟨lam, hlam0, hlam1, hlam2, S⟩ := exists_lam_extSettingW_near hh hr₁ hr₂ hI hV hVb hdeg hdeg4
      hPi₂ hGam₁ hGam₂ hCPi₂ hdPi hdGam hCdGam g₁ g₂ hN' hIp hNN hε
    have hb := hc (TwoModel.modelSum (lam := lam) hr₁.poly hr₂.poly) (TwoModel.intSum P I) S
      (TwoModel.abs_intSum_single_le P hCI) hx hy hxy (Sum.inr j) hj
    have hlami : 0 < lam⁻¹ := inv_pos.2 hlam0
    set Δ : ℝ := M₁.gammaMap y x (I (Pi.single i 1)) j - M₂.gammaMap y x (I (Pi.single i 1)) j
      with hΔ
    have hcomp : (TwoModel.modelSum (lam := lam) hr₁.poly hr₂.poly).gammaMap y x
        (TwoModel.intSum P I (Pi.single (Sum.inl ⟨i, hip⟩) 1)) (Sum.inr j) = lam⁻¹ * Δ := by
      rw [TwoModel.gammaMap_modelSum, TwoModel.single_inl, TwoModel.intSum_pairVec,
        TwoModel.gammaSum_apply_inr, TwoModel.leftPart_pairVec, TwoModel.rightPart_pairVec,
        TwoModel.extendNP_single, map_zero,
        TwoModel.extendNP_restrictNP_of_poly_zero (hIp _ hVi)]
      simp [hΔ]
    rw [hcomp] at hb
    have hΔb : |Δ| ≤ lam * (c * (CI + max CPi₂ (lam⁻¹ * CdPi) *
        max (max (max (max CGam₁ 1) (max CGam₂ 1)) (lam⁻¹ * CdGam)) 1) *
        max (max (max (max CGam₁ 1) (max CGam₂ 1)) (lam⁻¹ * CdGam)) 1 * T) := by
      have h1 : |lam⁻¹ * Δ| = lam⁻¹ * |Δ| := by rw [abs_mul, abs_of_pos hlami]
      rw [h1] at hb
      have h2 : |Δ| = lam * (lam⁻¹ * |Δ|) := by field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left hb hlam0.le
    have hGoverall : max (max (max (max CGam₁ 1) (max CGam₂ 1)) (lam⁻¹ * CdGam)) 1 ≤ G := by
      refine max_le (max_le (max_le (max_le ?_ hG1) (max_le ?_ hG1)) ?_) hG1
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · rw [inv_mul_le_iff₀ hlam0]; exact hlam2
    have hGp : 0 ≤ max (max (max (max CGam₁ 1) (max CGam₂ 1)) (lam⁻¹ * CdGam)) 1 :=
      zero_le_one.trans (le_max_right _ _)
    have hmaxnn : 0 ≤ max CPi₂ (lam⁻¹ * CdPi) := hCPi₂.trans (le_max_left _ _)
    have hP : lam * max CPi₂ (lam⁻¹ * CdPi) ≤ lam * CPi₂ + CdPi := by
      have : max CPi₂ (lam⁻¹ * CdPi) ≤ CPi₂ + lam⁻¹ * CdPi :=
        max_le (le_add_of_nonneg_right (mul_nonneg hlami.le hCdPi))
          (le_add_of_nonneg_left hCPi₂)
      calc lam * max CPi₂ (lam⁻¹ * CdPi) ≤ lam * (CPi₂ + lam⁻¹ * CdPi) :=
            mul_le_mul_of_nonneg_left this hlam0.le
        _ = lam * CPi₂ + CdPi := by field_simp
    have hcT : 0 ≤ c * T := mul_nonneg hc0 hT0
    calc |Δ| ≤ lam * (c * (CI + max CPi₂ (lam⁻¹ * CdPi) *
          max (max (max (max CGam₁ 1) (max CGam₂ 1)) (lam⁻¹ * CdGam)) 1) *
          max (max (max (max CGam₁ 1) (max CGam₂ 1)) (lam⁻¹ * CdGam)) 1 * T) := hΔb
      _ ≤ lam * (c * (CI + max CPi₂ (lam⁻¹ * CdPi) * G) * G * T) := by
          refine mul_le_mul_of_nonneg_left ?_ hlam0.le
          have h1 : CI + max CPi₂ (lam⁻¹ * CdPi) *
              max (max (max (max CGam₁ 1) (max CGam₂ 1)) (lam⁻¹ * CdGam)) 1 ≤
              CI + max CPi₂ (lam⁻¹ * CdPi) * G :=
            add_le_add_right (mul_le_mul_of_nonneg_left hGoverall hmaxnn) _
          have h2 : 0 ≤ CI + max CPi₂ (lam⁻¹ * CdPi) * G :=
            add_nonneg hCI0 (mul_nonneg hmaxnn hG0.le)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) hGoverall hGp
              (mul_nonneg hc0 h2)) hT0
      _ = c * T * (lam * CI * G + (lam * max CPi₂ (lam⁻¹ * CdPi)) * G * G) := by ring
      _ ≤ c * T * (lam * CI * G + (lam * CPi₂ + CdPi) * G * G) := by
          refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) hcT
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP hG0.le) hG0.le
      _ ≤ c * T * ((CdGam / G + ε) * CI * G + ((CdGam / G + ε) * CPi₂ + CdPi) * G * G) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hcT
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlam1 hCI0) hG0.le
          · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hG0.le) hG0.le
            have := mul_le_mul_of_nonneg_right hlam1 hCPi₂
            linarith
      _ = c * (CdPi * G * G + CdGam * (CI + CPi₂ * G)) * T +
            ε * (c * (CI * G + CPi₂ * G * G) * T) := by
          field_simp
          ring

end Model

end RegularityStructures

end
