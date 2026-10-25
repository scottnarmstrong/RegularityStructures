/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Phi4FixedPointWinNearOne
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.BlockInvariant
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# One-coefficient bound for the integration operator applied to a cube

For the window fixed-point operator `𝒦` (characterised on the time slab by
`(𝒦 g).val x = lowerProj deg γ₀ (kGammaRemG … (blockProj g).val x)`), the coefficients
`(𝒦 (U³)).val x i` with `deg i < γ₀` obey the pointwise bound of Hairer's Theorem 7.1,
`C₀ K₁ ‖U³‖ · singularWeight timeZeroDist x ^ (min ζ η'' + 2 - deg i)`, with
`‖U³‖ ≤ c² (R₀ + 1)³ (1 + C_Γ)⁴`.
-/

public section

namespace RegularityStructures.Phi43.TimeSlice

open RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- **One-coefficient bound for `𝒦 (U³)`** (near-`1` `Γ`-hypotheses). -/
theorem exists_abs_kernel_cube_apply_le (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)}
    {α γ₀ η₀ η' η'' ζ : ℝ} {N N' : ℕ} {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N)
    (Ppoly : PolynomialSector 𝒯 N') (A : Finset ι) (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α)
    (hγK : γ₀ ≤ γ₀ + α + α + 2)
    (hAζ : ∀ i ∈ A, ζ ≤ 𝒯.deg i) (hζγ : ζ ≤ γ₀ + α + α) (hζη : -2 < min ζ η'')
    (hγpos : 0 < γ₀ + α + α) (hdeg : ∀ j, 𝒯.deg j < γ₀ + α + α → -4 < 𝒯.deg j)
    (hN : N' ≤ N)
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ₀ + α + α + 2 → multiDeg l < N')
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ₀ + α + α + 2 - multiDeg k)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ i, i ∉ Set.range Ppoly.emb → ζ ≤ 𝒯.deg i → 𝒯.deg i < γ₀ + α + α →
        (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (hVA : 𝒯.IsSector (blockSpan A)) (hAG : 𝒯.IsBlockInvariant A) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      {CPi CGam CI CΓ CGam₁ CΓ₁ R₀ T : ℝ},
      M.PiBoundOn (γ₀ + α + α) CPi hairerTimeWindow →
      M.GammaBoundNearOn (γ₀ + α + α) CGam₁ 1 hairerTimeWindow →
      gammaChainConst (Fintype.card ι) CGam₁ 16 ≤ CGam →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M.GrowthModel (γ₀ + α + α) C' C'' ρP ρG p q) → 0 ≤ CPi →
      M.IsRealisingP h (γ₀ + α + α) Ppoly I (blockSpan A) →
      IsAbstractIntegration Ppoly (blockSpan A) I 2 →
      (∀ a ∈ blockSpan A, ∀ kk : PolyIndex N', I a (Ppoly.emb kk) = 0) →
      (∀ i j, |I (Pi.single i 1) j| ≤ CI) → 0 ≤ CI →
      M.GammaBoundNearOn γ₀ CΓ₁ 1 (timeSlab T) → M.GammaBoundNearOn (γ₀ + α) CΓ₁ 1 (timeSlab T) →
      M.GammaBoundNearOn (γ₀ + α + α + 2) CΓ₁ 1 (timeSlab T) →
      gammaChainConst (Fintype.card ι) CΓ₁ 16 ≤ CΓ → 0 ≤ CΓ → T ≤ 1 →
      ∀ 𝒦 : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) →ₗ[ℝ]
          M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T),
        (∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T), ∀ x ∈ timeSlab T,
          (𝒦 g).val x = lowerProj 𝒯.deg γ₀
            (M.kGammaRemG h r Ppoly I (γ₀ + α + α)
              (Model.SlabSpace.blockProj A (Model.gammaMap_blockProj_of_isBlockInvariant hAG M)
                g).val x)) →
        ∀ U : M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T), ‖U‖ ≤ R₀ + 1 →
          ∀ x ∈ timeSlab T, ∀ i, 𝒯.deg i < γ₀ →
            |(𝒦 (Model.SlabSpace.cube P (γ₀ + α + α) η'' U)).val x i| ≤
              C₀ * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ) *
                (P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4) *
                singularWeight timeZeroDist x ^ (min ζ η'' + 2 - 𝒯.deg i) := by
  classical
  obtain ⟨C₀, hC₀, hspec⟩ := Model.exists_singularBoundOn_kGammaRemG_win_near (γ₀ + α + α) η'' ζ N
    Ppoly hp hγpos hdeg hζγ hζη hN hNγ hnat hni hVA (isCoordClosed_blockSpan A)
    (fun i hi => hAζ i (mem_of_single_mem_blockSpan hi))
  refine ⟨C₀, hC₀, ?_⟩
  intro M I CPi CGam CI CΓ CGam₁ CΓ₁ R₀ T hPi hGam hCG hgr hCPi hreal hInt hIp hCI hCI0 hΓ₀ hΓ₁ hΓK
    hCΓr hCΓ hT1 𝒦 h𝒦 U hU x hx i hi
  have hS₀ := segmentClosed_timeSlab T
  have hGn := (hGam.toGammaNearOn M segmentClosed_hairerTimeWindow).mono M hCG
  have hΓ₀' := (hΓ₀.toGammaNearOn M hS₀).mono M hCΓr
  have hΓ₁' := (hΓ₁.toGammaNearOn M hS₀).mono M hCΓr
  have hΓK' := (hΓK.toGammaNearOn M hS₀).mono M hCΓr
  have hA := Model.gammaMap_blockProj_of_isBlockInvariant hAG M
  set g := Model.SlabSpace.cube P (γ₀ + α + α) η'' U with hg
  have hS := Model.layerSettingW_blockProj_near A hA g hγpos hPi hCPi hGn hgr hT1 hdeg hAζ hζγ hζη
  have hfA : ∀ z, (Model.SlabSpace.blockProj A hA g).val z ∈ blockSpan A := fun z =>
    mem_blockSpan_of_forall fun i hi => by
      rw [Model.SlabSpace.val_blockProj]
      exact blockProj_apply_of_notMem hi _
  obtain ⟨-, -, hpt⟩ := hspec M (Model.SlabSpace.blockProj A hA g).val T
    ‖Model.SlabSpace.blockProj A hA g‖ CPi CGam CI CΓ I hS hreal hInt hIp hCI hfA hΓK'
  have hK : 0 ≤ C₀ * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ) := by
    have h1 : 0 ≤ max 1 CGam := zero_le_one.trans (le_max_left _ _)
    have h2 : 0 ≤ max 1 CΓ := zero_le_one.trans (le_max_left _ _)
    positivity
  have hcube : ‖g‖ ≤ P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 := by
    refine (Model.SlabSpace.norm_cube_le_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
      hη''₁ hη''₂ hη''₃ hη''γ U hΓ₀' hΓ₁' hCΓ).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg U) hU 3
    have h4 : 0 ≤ P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 := by
      have := P.truncMulConst_nonneg
      positivity
    calc P.truncMulConst ^ 2 * ‖U‖ ^ 3 * (1 + CΓ) ^ 4
        = (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) * ‖U‖ ^ 3 := by ring
      _ ≤ (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) * (R₀ + 1) ^ 3 := by gcongr
      _ = _ := by ring
  have hbp : ‖Model.SlabSpace.blockProj A hA g‖ ≤ P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 *
      (1 + CΓ) ^ 4 := (Model.SlabSpace.norm_blockProj_le A hA g).trans hcube
  rw [h𝒦 g x hx, lowerProj_apply_of_lt hi]
  refine (hpt x hx i (hi.trans_le hγK)).trans ?_
  have hw : 0 ≤ singularWeight timeZeroDist x ^ (min ζ η'' + 2 - 𝒯.deg i) :=
    Real.rpow_nonneg (Layer.singularWeight_nonneg x) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbp hK) hw

end RegularityStructures.Phi43.TimeSlice

end
