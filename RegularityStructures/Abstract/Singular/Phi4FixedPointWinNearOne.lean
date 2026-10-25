/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Phi4FixedPointWinNear
public import RegularityStructures.Abstract.ModelNearChainDiff
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.BlockInvariant
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# Fixed point with near-`1` `Γ`-hypotheses

Window fixed point `exists_unique_phi4_fixedPoint_causal_win_near` with every `Γ`-hypothesis replaced by its near-`1` version (`GammaBoundNearOn γ C 1 S`); the near-`4` constants are `gammaChainConst |ι| C 16` (`GammaBoundNearOn.toGammaNearOn`), supplied by the relations `gammaChainConst .. ≤ CGam`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)} {α γ₀ η₀ η' η'' ζ : ℝ}
  {N N' : ℕ} {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N) (Ppoly : PolynomialSector 𝒯 N') (A : Finset ι)

include P Ppoly A hp

/-- **Window fixed point with near-`1` `Γ`-bounds only.** -/
theorem exists_unique_phi4_fixedPoint_causal_win_nearOne (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
    (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
    (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
    (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
    (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α) (hVc : IsCoordClosed V)
    (hγK : γ₀ ≤ γ₀ + α + α + 2) (hηK : η₀ < min ζ η'' + 2) (hηγ : η₀ < γ₀)
    (hAζ : ∀ i ∈ A, ζ ≤ 𝒯.deg i) (hζγ : ζ ≤ γ₀ + α + α) (hζη : -2 < min ζ η'')
    (hγpos : 0 < γ₀ + α + α) (hdeg : ∀ j, 𝒯.deg j < γ₀ + α + α → -4 < 𝒯.deg j)
    (hN : N' ≤ N)
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ₀ + α + α + 2 → multiDeg l < N')
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ₀ + α + α + 2 - multiDeg k)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ i, i ∉ Set.range Ppoly.emb → ζ ≤ 𝒯.deg i → 𝒯.deg i < γ₀ + α + α →
        (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (hVA : 𝒯.IsSector (blockSpan A)) (hAG : 𝒯.IsBlockInvariant A)
    (hpolyV : ∀ k : PolyIndex N', polyDeg N' k < γ₀ + α + α + 2 →
      (Pi.single (Ppoly.emb k) 1 : ι → ℝ) ∈ V) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      {CPi CGam CI CΓ CGam₁ CΓ₁ R₀ T : ℝ} (v : M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)),
      M.PiBoundOn (γ₀ + α + α) CPi hairerTimeWindow →
      M.GammaBoundNearOn (γ₀ + α + α) CGam₁ 1 hairerTimeWindow →
      gammaChainConst (Fintype.card ι) CGam₁ 16 ≤ CGam →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M.GrowthModel (γ₀ + α + α) C' C'' ρP ρG p q) → 0 ≤ CPi → M.IsJointMeasurable →
      M.IsRealisingP h (γ₀ + α + α) Ppoly I (blockSpan A) →
      IsAbstractIntegration Ppoly (blockSpan A) I 2 →
      (∀ a ∈ blockSpan A, ∀ kk : PolyIndex N', I a (Ppoly.emb kk) = 0) →
      (∀ i j, |I (Pi.single i 1) j| ≤ CI) →
      (∀ a ∈ blockSpan A, I a ∈ V) →
      M.GammaBoundNearOn γ₀ CΓ₁ 1 (timeSlab T) → M.GammaBoundNearOn (γ₀ + α) CΓ₁ 1 (timeSlab T) →
      M.GammaBoundNearOn (γ₀ + α + α + 2) CΓ₁ 1 (timeSlab T) →
      gammaChainConst (Fintype.card ι) CΓ₁ 16 ≤ CΓ → 0 ≤ CΓ → 0 ≤ R₀ →
      0 < T → T ≤ 1 →
      T ≤ fixedPointTime
        (C₀ * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ) *
          (1 + Fintype.card ι * CΓ))
        ((min (min ζ η'' + 2) γ₀ - η₀) / 2) (3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) 0 R₀ 2 →
      ‖v‖ ≤ R₀ →
      ∃ 𝒦 : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) →ₗ[ℝ]
          M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T),
        (∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T), ∀ x ∈ timeSlab T,
          (𝒦 g).val x = lowerProj 𝒯.deg γ₀
            (M.kGammaRemG h r Ppoly I (γ₀ + α + α) (SlabSpace.blockProj A (gammaMap_blockProj_of_isBlockInvariant hAG M) g).val x)) ∧
        ∃! U : M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T), ‖U‖ ≤ R₀ + 1 ∧
          U = -𝒦 (SlabSpace.cube P (γ₀ + α + α) η'' U) + v := by
  classical
  obtain ⟨C₀, hC₀, hmain⟩ := exists_unique_phi4_fixedPoint_causal_win_near P hp Ppoly A hV hW hVα hWα
    hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ hVc hγK hηK hηγ hAζ hζγ hζη hγpos
    hdeg hN hNγ hnat hni hVA hAG hpolyV
  refine ⟨C₀, hC₀, fun M I CPi CGam CI CΓ CGam₁ CΓ₁ R₀ T v hPi hGam hCG hgr hCPi hJ hreal hInt hIp
    hCI hIV hΓ₀ hΓ₁ hΓK hCΓr hCΓ hR₀ hT hT1 hTT₀ hv => ?_⟩
  have hS₀ := segmentClosed_timeSlab T
  exact hmain M I v hPi
    (((hGam.toGammaNearOn M segmentClosed_hairerTimeWindow).mono M hCG)) hgr hCPi hJ hreal hInt hIp
    hCI hIV
    ((hΓ₀.toGammaNearOn M hS₀).mono M hCΓr) ((hΓ₁.toGammaNearOn M hS₀).mono M hCΓr)
    ((hΓK.toGammaNearOn M hS₀).mono M hCΓr) hCΓ hR₀ hT hT1 hTT₀ hv

end Model

end RegularityStructures

end
