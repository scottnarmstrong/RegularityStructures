/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.PairingDiff
public import Phi43.Potential.NearPairing
public import RegularityStructures.Abstract.Singular.TwoModel.BoundsNear
public import Phi43.Potential.TestFunction
public import RegularityStructures.Abstract.Integration.Commute.Reg
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Near-pair `Γ` version of `Phi43.Potential.PairingDiff`

Two-model derivative bounds of `Q ∗ ξ` with `GammaNearOn`/`GammaDiffNearOn` hypotheses.
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {M₁ M₂ : Model 𝒯 parabolicSemigroup}

/-- **Two-model derivative bound of `Q ∗ ξ`**, with the parameter `λ` of the difference model. -/
theorem abs_ddA_potConv_sub_le_near {lam : ℝ} (hlam : 0 < lam)
    (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    {γ CPi₂ CGam₁ CGam₂ CdPi CdGam : ℝ}
    (hPi₂ : M₂.PiBoundOn γ CPi₂ hairerTimeWindow) (hCPi₂ : 0 ≤ CPi₂)
    (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow)
    (hGam₁ : M₁.GammaNearOn γ CGam₁ hairerTimeWindow)
    (hGam₂ : M₂.GammaNearOn γ CGam₂ hairerTimeWindow)
    (hdGam : M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow)
    (h0 : 0 ≤ max (max CGam₁ CGam₂) (lam⁻¹ * CdGam))
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {o : ι} (ho : 𝒯.deg o < γ) (hnp : o ∉ Set.range P.emb)
    {ξ₁ ξ₂ : ParabolicSpace → ℝ} (hp₁ : PolyBounded ξ₁) (hp₂ : PolyBounded ξ₂)
    (hξ₁ : Continuous ξ₁) (hξ₂ : Continuous ξ₂)
    (hreg₁ : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M₁.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ₁ y)
    (hreg₂ : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M₂.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ₂ y)
    (hgrowth₁ : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M₁.HasQualitativeGrowthAt γ z)
    (hgrowth₂ : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M₂.HasQualitativeGrowthAt γ z)
    (N : ℕ) (l : List (Fin 4)) {z : ParabolicSpace} (hz0 : 0 ≤ z.1) (hz1 : z.1 ≤ 1) :
    |ddA l (potConv ξ₁ (potQ N)) z - ddA l (potConv ξ₂ (potQ N)) z| ≤
      lam * (r4ModelConst (TwoModel.structSumU P) γ *
        (max 1 (max (max CGam₁ CGam₂) (lam⁻¹ * CdGam)) * max CPi₂ (lam⁻¹ * CdPi)) *
        potTestConst N l) := by
  set Ms := TwoModel.modelSum (lam := lam) h₁ h₂ with hMs
  have hPiS := TwoModel.piBoundOn_modelSum h₁ h₂ hlam hPi₂ hdPi
  have hGamS := TwoModel.gammaBoundOn_modelSum_near h₁ h₂ hlam h0 hGam₁ hGam₂ hdGam
  have hCPiS : 0 ≤ max CPi₂ (lam⁻¹ * CdPi) := hCPi₂.trans (le_max_left _ _)
  have hdegS := hdeg_structSumU P hdeg
  set o' : TwoModel.NonPoly P ⊕ ι := Sum.inl ⟨o, hnp⟩ with ho'
  have hoS : (TwoModel.structSumU P).deg o' < γ := ho
  have hpΔ : PolyBounded (fun w => lam⁻¹ * (ξ₁ w - ξ₂ w)) := (hp₁.sub hp₂).const_mul _
  obtain ⟨-, BΔ, nΔ, hBΔ⟩ := hpΔ
  have hcΔ : Continuous (fun w => lam⁻¹ * (ξ₁ w - ξ₂ w)) :=
    continuous_const.mul (hξ₁.sub hξ₂)
  have hregS : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      Ms.regPi x (Pi.single o' 1) t y =
        parabolicSemigroup.apply t (fun w => lam⁻¹ * (ξ₁ w - ξ₂ w)) y := by
    intro x t ht y
    rw [hMs, TwoModel.regPi_modelSum, ho', TwoModel.coe_piSum_single_inl, hreg₁ x t ht,
      hreg₂ x t ht, TwoModel.apply_const_mul_sub hp₁ hp₂ _ ht]
  have hgS : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → Ms.HasQualitativeGrowthAt γ z :=
    fun z a b => hasQualitativeGrowthAt_modelSum hlam h₁ h₂ (hgrowth₁ z a b) (hgrowth₂ z a b)
  have h := abs_ddA_potConv_le_near Ms hPiS hCPiS hGamS hdegS hoS hcΔ hBΔ hregS hgS N l hz0 hz1
  rw [ddA_potConv hcΔ (contDiff_potQ N) (hasCompactSupport_ddA_potQ N) l z,
    potConv_const_mul_sub hξ₁ hξ₂ _ N l z, abs_mul, abs_of_pos (inv_pos.2 hlam),
    ← ddA_potConv hξ₁ (contDiff_potQ N) (hasCompactSupport_ddA_potQ N) l z,
    ← ddA_potConv hξ₂ (contDiff_potQ N) (hasCompactSupport_ddA_potQ N) l z] at h
  rw [inv_mul_le_iff₀ hlam] at h
  exact h

/-- **Two-model derivative bound of `Q ∗ ξ` in the size `d` of the model difference**: if
`CdPi, CdGam ≤ d` the bound is `d · K · potTestConst N l` with `K` depending only on the
constants of the two models (and `r4ModelConst` of the sum structure). -/
theorem abs_ddA_potConv_sub_le_of_diff_near
    (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P)
    {γ CPi₂ CGam₁ CGam₂ CdPi CdGam d : ℝ}
    (hPi₂ : M₂.PiBoundOn γ CPi₂ hairerTimeWindow) (hCPi₂ : 0 ≤ CPi₂)
    (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi hairerTimeWindow)
    (hGam₁ : M₁.GammaNearOn γ CGam₁ hairerTimeWindow)
    (hGam₂ : M₂.GammaNearOn γ CGam₂ hairerTimeWindow)
    (hdGam : M₁.GammaDiffNearOn M₂ γ CdGam hairerTimeWindow)
    (hCGam₁ : 0 ≤ CGam₁) (hCdPi : CdPi ≤ d) (hCdGam : CdGam ≤ d) (hd : 0 ≤ d)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {o : ι} (ho : 𝒯.deg o < γ) (hnp : o ∉ Set.range P.emb)
    {ξ₁ ξ₂ : ParabolicSpace → ℝ} (hp₁ : PolyBounded ξ₁) (hp₂ : PolyBounded ξ₂)
    (hξ₁ : Continuous ξ₁) (hξ₂ : Continuous ξ₂)
    (hreg₁ : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M₁.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ₁ y)
    (hreg₂ : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M₂.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ₂ y)
    (hgrowth₁ : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M₁.HasQualitativeGrowthAt γ z)
    (hgrowth₂ : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M₂.HasQualitativeGrowthAt γ z)
    (N : ℕ) (l : List (Fin 4)) {z : ParabolicSpace} (hz0 : 0 ≤ z.1) (hz1 : z.1 ≤ 1) :
    |ddA l (potConv ξ₁ (potQ N)) z - ddA l (potConv ξ₂ (potQ N)) z| ≤
      d * (r4ModelConst (TwoModel.structSumU P) γ *
        (max 1 (max CGam₁ CGam₂) * max CPi₂ 1) * potTestConst N l) := by
  set K := r4ModelConst (TwoModel.structSumU P) γ *
        (max 1 (max CGam₁ CGam₂) * max CPi₂ 1) * potTestConst N l with hK
  have hr := r4ModelConst_nonneg (TwoModel.structSumU P) (hdeg_structSumU P hdeg)
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg hr (mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (zero_le_one.trans (le_max_right _ _)))) (potTestConst_pos N l).le
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set lam := d + ε / (K + 1) with hlamdef
  have hKp : 0 < K + 1 := by linarith
  have hlam : 0 < lam := by have := div_pos hε hKp; linarith
  have hdl : d ≤ lam := by have := div_pos hε hKp; linarith
  have h0 : 0 ≤ max (max CGam₁ CGam₂) (lam⁻¹ * CdGam) :=
    hCGam₁.trans ((le_max_left _ _).trans (le_max_left _ _))
  have h := abs_ddA_potConv_sub_le_near hlam h₁ h₂ hPi₂ hCPi₂ hdPi hGam₁ hGam₂ hdGam h0 hdeg ho hnp hp₁
    hp₂ hξ₁ hξ₂ hreg₁ hreg₂ hgrowth₁ hgrowth₂ N l hz0 hz1
  refine h.trans ?_
  have g1 : max 1 (max (max CGam₁ CGam₂) (lam⁻¹ * CdGam)) ≤ max 1 (max CGam₁ CGam₂) :=
    max_le (le_max_left _ _) (max_le (le_max_right _ _)
      ((potInvMul_le_one hlam (hCdGam.trans hdl)).trans (le_max_left _ _)))
  have g2 : max CPi₂ (lam⁻¹ * CdPi) ≤ max CPi₂ 1 :=
    max_le (le_max_left _ _) ((potInvMul_le_one hlam (hCdPi.trans hdl)).trans
      (le_max_right _ _))
  have g3 : 0 ≤ max CPi₂ (lam⁻¹ * CdPi) := hCPi₂.trans (le_max_left _ _)
  have g4 : 0 ≤ max 1 (max (max CGam₁ CGam₂) (lam⁻¹ * CdGam)) := zero_le_one.trans (le_max_left _ _)
  have hle : r4ModelConst (TwoModel.structSumU P) γ *
        (max 1 (max (max CGam₁ CGam₂) (lam⁻¹ * CdGam)) * max CPi₂ (lam⁻¹ * CdPi)) *
        potTestConst N l ≤ K := by
    rw [hK]
    have hA := (potTestConst_pos N l).le
    gcongr
  calc lam * (r4ModelConst (TwoModel.structSumU P) γ *
        (max 1 (max (max CGam₁ CGam₂) (lam⁻¹ * CdGam)) * max CPi₂ (lam⁻¹ * CdPi)) *
        potTestConst N l) ≤ lam * K := mul_le_mul_of_nonneg_left hle hlam.le
    _ = d * K + ε * (K / (K + 1)) := by rw [hlamdef]; field_simp
    _ ≤ d * K + ε := by
        have : K / (K + 1) ≤ 1 := by rw [div_le_one hKp]; linarith
        nlinarith

end RegularityStructures.Potential

end
