/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TimeSlice.OneCoeff
public import Phi43.TimeSlice.AbstractTwo
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# Lipschitz dependence of the `1`-coefficient of `𝒦 (U³)` on the model and on `U`

Two-model version of `phi43_one_coeff_fixedPoint_le` at the `Φ⁴₃` data of
`phi43FixedPointF_window_nearOne`.
-/

public section

namespace RegularityStructures.Phi43.TimeSlice

open RegularityStructures

/-- **Difference of the `1`-coefficients of `𝒦₁ (U₁³)` and `𝒦₂ (U₂³)`.** -/
theorem phi43_one_coeff_fixedPoint_diff_le (κ : Kappa) {η : ℝ} (hη₁ : -2 / 3 < η)
    (hκη : κ.1 < -1 / 2 - η) {N : ℕ} (hN : 3 ≤ N) {h r : ParabolicSpace → ℝ}
    (hp : KernelPair h r N) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup)
        {CPi CGam CΓ CGam₁ CΓ₁ δ₁ R₀ T δ δU : ℝ},
      M₁.PiBoundOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CPi hairerTimeWindow →
      M₂.PiBoundOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CPi hairerTimeWindow →
      M₁.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CGam₁ 1 hairerTimeWindow →
      M₂.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ) CGam₁ 1 hairerTimeWindow →
      gammaChainConst (Fintype.card SymbolF) CGam₁ 16 ≤ CGam →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₁.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q) →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₂.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q) →
      0 ≤ CPi →
      M₁.IsRealisingP h (gamma κ + phi43Alpha κ + phi43Alpha κ) (phi43PolynomialSectorF κ)
        phi43IntegrationF (blockSpan phi43XiFreeF) →
      M₂.IsRealisingP h (gamma κ + phi43Alpha κ + phi43Alpha κ) (phi43PolynomialSectorF κ)
        phi43IntegrationF (blockSpan phi43XiFreeF) →
      M₁.GammaBoundNearOn (gamma κ) CΓ₁ 1 (timeSlab T) →
      M₁.GammaBoundNearOn (gamma κ + phi43Alpha κ) CΓ₁ 1 (timeSlab T) →
      M₁.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ + 2) CΓ₁ 1 (timeSlab T) →
      M₂.GammaBoundNearOn (gamma κ) CΓ₁ 1 (timeSlab T) →
      M₂.GammaBoundNearOn (gamma κ + phi43Alpha κ) CΓ₁ 1 (timeSlab T) →
      M₂.GammaBoundNearOn (gamma κ + phi43Alpha κ + phi43Alpha κ + 2) CΓ₁ 1 (timeSlab T) →
      gammaChainConst (Fintype.card SymbolF) CΓ₁ 16 ≤ CΓ → 0 ≤ CΓ →
      M₁.PiDiffBoundOn M₂ (gamma κ + phi43Alpha κ + phi43Alpha κ) δ hairerTimeWindow →
      M₁.GammaDiffBoundNearOn M₂ (gamma κ + phi43Alpha κ + phi43Alpha κ) δ₁ 1
        hairerTimeWindow →
      gammaDiffChainConst (Fintype.card SymbolF) CGam₁ δ₁ 16 ≤ δ →
      M₁.GammaDiffBoundNearOn M₂ (gamma κ) δ₁ 1 (timeSlab T) →
      M₁.GammaDiffBoundNearOn M₂ (gamma κ + phi43Alpha κ) δ₁ 1 (timeSlab T) →
      M₁.GammaDiffBoundNearOn M₂ (gamma κ + phi43Alpha κ + phi43Alpha κ + 2) δ₁ 1
        (timeSlab T) →
      gammaDiffChainConst (Fintype.card SymbolF) CΓ₁ δ₁ 16 ≤ δ → 0 ≤ δ → 0 ≤ δU → 0 ≤ R₀ →
      T ≤ 1 →
      ∀ (𝒦₁ : M₁.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab T) →ₗ[ℝ] M₁.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T))
        (𝒦₂ : M₂.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab T) →ₗ[ℝ] M₂.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)),
        (∀ g, ∀ x ∈ timeSlab T, (𝒦₁ g).val x =
          lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
            (M₁.kGammaRemG h r (phi43PolynomialSectorF κ) phi43IntegrationF
              (gamma κ + phi43Alpha κ + phi43Alpha κ)
              (Model.SlabSpace.blockProj phi43XiFreeF
                (Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M₁)
                g).val x)) →
        (∀ g, ∀ x ∈ timeSlab T, (𝒦₂ g).val x =
          lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
            (M₂.kGammaRemG h r (phi43PolynomialSectorF κ) phi43IntegrationF
              (gamma κ + phi43Alpha κ + phi43Alpha κ)
              (Model.SlabSpace.blockProj phi43XiFreeF
                (Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M₂)
                g).val x)) →
        ∀ (U₁ : M₁.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T))
          (U₂ : M₂.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)),
        ‖U₁‖ ≤ R₀ + 1 → ‖U₂‖ ≤ R₀ + 1 →
        M₁.SingularDiffBoundOn M₂ timeZeroDist (gamma κ) η δU (timeSlab T) U₁.val U₂.val →
        ∀ x ∈ timeSlab T,
          |(𝒦₁ (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
                (3 * η) U₁)).val x (SymbolF.old .one) -
            (𝒦₂ (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
                (3 * η) U₂)).val x (SymbolF.old .one)| ≤
            C₀ * ((((max 1 CGam * max CPi 1 +
              Fintype.card (TwoModel.NonPoly (phi43PolynomialSectorF κ) ⊕ SymbolF) * 1) *
              max 1 CΓ) * ((phi43ProductF κ).truncMulConst ^ 2 * (1 + CΓ) ^ 4 * 5)) *
              (R₀ + 1) ^ 3) * (δU + δ) * x.1 ^ ((3 * η + 2) / 2) := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  obtain ⟨C₀, hC₀, hspec⟩ := exists_abs_kernel_cube_sub_apply_le
    (𝒯 := phi43RegularityStructureF κ) (phi43ProductF κ) hp (phi43PolynomialSectorF κ)
    phi43XiFreeF (V := phi43SectorV) (W := phi43SectorW) (α := phi43Alpha κ) (γ₀ := gamma κ)
    (η₀ := η) (η' := 2 * η) (η'' := 3 * η) (ζ := phi43Zeta κ)
    (phi43SectorV_isSector κ) (phi43SectorW_isSector κ) (phi43SectorV_ofRegularity κ)
    (phi43SectorW_ofRegularity κ) (phi43ProductF_mul_mem κ) (phi43ProductF_isRegularPair_VV κ)
    (phi43ProductF_isRegularPair_VW κ)
    (by simp only [phi43Alpha]; linarith) (by linarith)
    (by simp only [gamma, phi43Alpha]; linarith) (by simp only [phi43Alpha]; linarith)
    (by simp only [phi43Alpha]; linarith) (by linarith)
    (by simp only [gamma, phi43Alpha]; linarith)
    (by simp only [gamma, phi43Alpha]; linarith)
    (fun i hi => phi43DegreeF_xiFree_ge κ hi)
    (by simp only [gamma, phi43Alpha, phi43Zeta]; linarith)
    (lt_min_iff.2 ⟨by simp only [phi43Zeta]; linarith, by linarith⟩)
    (by simp only [gamma, phi43Alpha]; linarith)
    (fun j _ => phi43DegreeF_gt_neg_four κ j) hN (phi43DegreeTwo_hNgamma κ)
    (fun k _ l => phi43_hnat κ k l) (fun k _ i hi _ _ => phi43_hni κ k i hi)
    (phi43XiFreeF_isSector κ) (phi43XiFreeF_isBlockInvariant κ)
  refine ⟨C₀, hC₀, ?_⟩
  intro M₁ M₂ CPi CGam CΓ CGam₁ CΓ₁ δ₁ R₀ T δ δU hPi₁ hPi₂ hG₁ hG₂ hCG gr₁ gr₂ hCPi hreal₁ hreal₂
    hΓ₁₀ hΓ₁₁ hΓ₁K hΓ₂₀ hΓ₂₁ hΓ₂K hCΓr hCΓ hdP hdG hdGr hdΓ₀ hdΓ₁ hdΓK hdΓr hδ hδU hR₀ hT1 𝒦₁
    𝒦₂ h𝒦₁ h𝒦₂ U₁ U₂ hU₁ hU₂ hUd x hx
  have hdeg : (phi43RegularityStructureF κ).deg (SymbolF.old .one) < gamma κ := by
    change homogeneity κ .one < gamma κ
    simp only [homogeneity, gamma]
    linarith
  have hb := hspec M₁ M₂ phi43IntegrationF (CI := 1) hPi₁ hPi₂ hG₁ hG₂ hCG gr₁ gr₂ hCPi hreal₁
    hreal₂ (phi43IntegrationF_isAbstractIntegration κ)
    (fun a _ kk => phi43IntegrationF_polyEmb_eq_zero κ a kk)
    (fun i j => phi43IntegrationF_single_abs_le i j) zero_le_one hΓ₁₀ hΓ₁₁ hΓ₁K hΓ₂₀ hΓ₂₁ hΓ₂K
    hCΓr hCΓ hdP hdG hdGr hdΓ₀ hdΓ₁ hdΓK hdΓr hδ hδU hR₀ hT1 𝒦₁ 𝒦₂ h𝒦₁ h𝒦₂ U₁ U₂ hU₁ hU₂ hUd
    x hx (SymbolF.old .one) hdeg
  have hmin : min (phi43Zeta κ) (3 * η) = 3 * η := by
    refine min_eq_right ?_
    simp only [phi43Zeta]
    linarith
  have hd : (phi43RegularityStructureF κ).deg (SymbolF.old .one) = 0 := rfl
  rw [hmin, hd, sub_zero, singularWeight_timeZeroDist_rpow_of_mem_timeSlab hT1 hx] at hb
  exact hb.trans (le_of_eq (by ring))

end RegularityStructures.Phi43.TimeSlice

end
