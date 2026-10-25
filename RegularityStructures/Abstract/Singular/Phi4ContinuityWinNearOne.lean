/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Phi4ContinuityWinNear
public import RegularityStructures.Abstract.ModelNearChainDiff
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.BlockInvariant
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# Continuity with near-`1` `Γ`-hypotheses

Continuity `singularDiffBoundOn_phi4_fixedPoint_causal_win_near` with every `Γ`-hypothesis replaced by its near-`1` version (`GammaBoundNearOn γ C 1 S`, `GammaDiffBoundNearOn M₂ γ δ 1 S`); the near-`4` constants are `gammaChainConst |ι| C 16` (`GammaBoundNearOn.toGammaNearOn`), supplied by the relations `gammaChainConst .. ≤ CGam` and `gammaDiffChainConst .. ≤ δ`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)} {α γ₀ η₀ η' η'' ζ : ℝ}
  {N N' : ℕ} {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N) (Ppoly : PolynomialSector 𝒯 N') (A : Finset ι)

include P Ppoly A hp

/-- **Lipschitz dependence of the window fixed point with near-`1` `Γ`-bounds only.** -/
theorem singularDiffBoundOn_phi4_fixedPoint_causal_win_nearOne (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α)
    (hγK : γ₀ ≤ γ₀ + α + α + 2) (hηK : η₀ < min ζ η'' + 2) (hηγ : η₀ < γ₀)
    (hAζ : ∀ i ∈ A, ζ ≤ 𝒯.deg i) (hζγ : ζ ≤ γ₀ + α + α) (hζη : -2 < min ζ η'')
    (hγpos : 0 < γ₀ + α + α) (hdeg : ∀ j, 𝒯.deg j < γ₀ + α + α → -4 < 𝒯.deg j)
    (hN : N' ≤ N)
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ₀ + α + α + 2 → multiDeg l < N')
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ₀ + α + α + 2 - multiDeg k)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ i, i ∉ Set.range Ppoly.emb → ζ ≤ 𝒯.deg i → 𝒯.deg i < γ₀ + α + α → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (hVA : 𝒯.IsSector (blockSpan A)) (hAG : 𝒯.IsBlockInvariant A) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (M₁ M₂ : Model 𝒯 parabolicSemigroup) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      {CPi CGam CI CΓ CGam₁ CΓ₁ δ₁ R₀ T δ δv : ℝ}
      (v₁ : M₁.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T))
      (v₂ : M₂.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)),
      M₁.PiBoundOn (γ₀ + α + α) CPi hairerTimeWindow →
      M₂.PiBoundOn (γ₀ + α + α) CPi hairerTimeWindow →
      M₁.GammaBoundNearOn (γ₀ + α + α) CGam₁ 1 hairerTimeWindow →
      M₂.GammaBoundNearOn (γ₀ + α + α) CGam₁ 1 hairerTimeWindow →
      gammaChainConst (Fintype.card ι) CGam₁ 16 ≤ CGam →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₁.GrowthModel (γ₀ + α + α) C' C'' ρP ρG p q) →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₂.GrowthModel (γ₀ + α + α) C' C'' ρP ρG p q) → 0 ≤ CPi →
      M₁.IsRealisingP h (γ₀ + α + α) Ppoly I (blockSpan A) →
      M₂.IsRealisingP h (γ₀ + α + α) Ppoly I (blockSpan A) →
      IsAbstractIntegration Ppoly (blockSpan A) I 2 →
      (∀ a ∈ blockSpan A, ∀ kk : PolyIndex N', I a (Ppoly.emb kk) = 0) →
      (∀ i j, |I (Pi.single i 1) j| ≤ CI) → 0 ≤ CI →
      M₁.GammaBoundNearOn γ₀ CΓ₁ 1 (timeSlab T) → M₁.GammaBoundNearOn (γ₀ + α) CΓ₁ 1 (timeSlab T) →
      M₁.GammaBoundNearOn (γ₀ + α + α + 2) CΓ₁ 1 (timeSlab T) →
      M₂.GammaBoundNearOn γ₀ CΓ₁ 1 (timeSlab T) → M₂.GammaBoundNearOn (γ₀ + α) CΓ₁ 1 (timeSlab T) →
      M₂.GammaBoundNearOn (γ₀ + α + α + 2) CΓ₁ 1 (timeSlab T) →
      gammaChainConst (Fintype.card ι) CΓ₁ 16 ≤ CΓ → 0 ≤ CΓ →
      M₁.PiDiffBoundOn M₂ (γ₀ + α + α) δ hairerTimeWindow →
      M₁.GammaDiffBoundNearOn M₂ (γ₀ + α + α) δ₁ 1 hairerTimeWindow →
      gammaDiffChainConst (Fintype.card ι) CGam₁ δ₁ 16 ≤ δ →
      M₁.GammaDiffBoundNearOn M₂ γ₀ δ₁ 1 (timeSlab T) →
      M₁.GammaDiffBoundNearOn M₂ (γ₀ + α) δ₁ 1 (timeSlab T) →
      M₁.GammaDiffBoundNearOn M₂ (γ₀ + α + α + 2) δ₁ 1 (timeSlab T) →
      gammaDiffChainConst (Fintype.card ι) CΓ₁ δ₁ 16 ≤ δ → 0 ≤ δ → 0 ≤ δv → 0 ≤ R₀ →
      0 < T → T ≤ 1 →
      T ≤ fixedPointTime
        (C₀ * ((max 1 CGam * max CPi 1 +
          Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
          (1 + Fintype.card ι * CΓ))
        ((min (min ζ η'' + 2) γ₀ - η₀) / 2) (3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) 0 R₀ 2 →
      ∀ (𝒦₁ : M₁.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) →ₗ[ℝ]
          M₁.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T))
        (𝒦₂ : M₂.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) →ₗ[ℝ]
          M₂.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)),
      (∀ g, ∀ x ∈ timeSlab T, (𝒦₁ g).val x = lowerProj 𝒯.deg γ₀
        (M₁.kGammaRemG h r Ppoly I (γ₀ + α + α) (SlabSpace.blockProj A (gammaMap_blockProj_of_isBlockInvariant hAG M₁) g).val x)) →
      (∀ g, ∀ x ∈ timeSlab T, (𝒦₂ g).val x = lowerProj 𝒯.deg γ₀
        (M₂.kGammaRemG h r Ppoly I (γ₀ + α + α) (SlabSpace.blockProj A (gammaMap_blockProj_of_isBlockInvariant hAG M₂) g).val x)) →
      M₁.SingularDiffBoundOn M₂ timeZeroDist γ₀ η₀ δv (timeSlab T) v₁.val v₂.val →
      ∀ (U₁ : M₁.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T))
        (U₂ : M₂.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)),
      ‖U₁‖ ≤ R₀ + 1 → ‖U₂‖ ≤ R₀ + 1 →
      U₁ = -𝒦₁ (SlabSpace.cube P (γ₀ + α + α) η'' U₁) + v₁ →
      U₂ = -𝒦₂ (SlabSpace.cube P (γ₀ + α + α) η'' U₂) + v₂ →
      M₁.SingularDiffBoundOn M₂ timeZeroDist γ₀ η₀
        (2 * (δv + C₀ * ((max 1 CGam * max CPi 1 +
              Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
              (1 + Fintype.card ι * CΓ) * T ^ ((min (min ζ η'' + 2) γ₀ - η₀) / 2) *
              (4 * P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 * δ) +
            T ^ ((min (min ζ η'' + 2) γ₀ - η₀) / 2) * δ *
              (P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4) *
              (C₀ * ((max 1 CGam * max CPi 1 +
                Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
                (1 + Fintype.card ι * CΓ + Fintype.card ι)))) (timeSlab T) U₁.val U₂.val := by
  classical
  obtain ⟨C₀, hC₀, hmain⟩ := singularDiffBoundOn_phi4_fixedPoint_causal_win_near P hp Ppoly A hV hW
    hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ hγK hηK hηγ hAζ hζγ hζη
    hγpos hdeg hN hNγ hnat hni hVA hAG
  refine ⟨C₀, hC₀, ?_⟩
  intro M₁ M₂ I CPi CGam CI CΓ CGam₁ CΓ₁ δ₁ R₀ T δ δv v₁ v₂ hPi₁ hPi₂ hG₁ hG₂ hCG gr₁ gr₂ hCPi
    hreal₁ hreal₂ hInt hIp hCI hCI0 hΓ₁₀ hΓ₁₁ hΓ₁K hΓ₂₀ hΓ₂₁ hΓ₂K hCΓr hCΓ hdP hdG hdGr hdΓ₀
    hdΓ₁ hdΓK hdΓr hδ hδv hR₀ hT hT1 hTT₀
  have hW := segmentClosed_hairerTimeWindow
  have hS := segmentClosed_timeSlab T
  have dW := (GammaDiffBoundNearOn.toGammaDiffNearOn hW hG₁ hG₂ hdG).mono_const hdGr
  have d₀ := (GammaDiffBoundNearOn.toGammaDiffNearOn hS hΓ₁₀ hΓ₂₀ hdΓ₀).mono_const hdΓr
  have d₁ := (GammaDiffBoundNearOn.toGammaDiffNearOn hS hΓ₁₁ hΓ₂₁ hdΓ₁).mono_const hdΓr
  have dK := (GammaDiffBoundNearOn.toGammaDiffNearOn hS hΓ₁K hΓ₂K hdΓK).mono_const hdΓr
  exact hmain M₁ M₂ I v₁ v₂ hPi₁ hPi₂
    ((hG₁.toGammaNearOn M₁ hW).mono M₁ hCG) ((hG₂.toGammaNearOn M₂ hW).mono M₂ hCG) gr₁ gr₂ hCPi
    hreal₁ hreal₂ hInt hIp hCI hCI0
    ((hΓ₁₀.toGammaNearOn M₁ hS).mono M₁ hCΓr) ((hΓ₁₁.toGammaNearOn M₁ hS).mono M₁ hCΓr)
    ((hΓ₁K.toGammaNearOn M₁ hS).mono M₁ hCΓr) ((hΓ₂₀.toGammaNearOn M₂ hS).mono M₂ hCΓr)
    ((hΓ₂₁.toGammaNearOn M₂ hS).mono M₂ hCΓr) ((hΓ₂K.toGammaNearOn M₂ hS).mono M₂ hCΓr) hCΓ
    hdP dW d₀ d₁ dK hδ hδv hR₀ hT hT1 hTT₀

end Model

end RegularityStructures

end
