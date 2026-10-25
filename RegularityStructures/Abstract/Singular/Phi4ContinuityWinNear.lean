/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointPhi4Near
public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.Singular.Diff.TruncationNear
public import RegularityStructures.Abstract.Singular.Phi4ContinuityNonnegWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.BlockInvariant
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# Continuity of the abstract `Φ⁴₃` fixed point in the model and the data, near-pair `Γ`-bounds

[Hai14, Thm. 7.8 (last statement), Prop. 9.8]: the `Φ⁴₃` fixed point depends Lipschitz continuously
on `(v, Z)` (`singularDiffBoundOn_phi4_fixedPoint_causal_win_near`). Both models have model bounds
on `hairerTimeWindow` and a qualitative growth model (used only for identities, convergence and
measurability); the model difference is controlled by `PiDiffBoundOn` and `GammaDiffNearOn` on
`hairerTimeWindow`; the constant involves `max 1 CGam * max CPi 1` and no weights; the block
invariance is the structural hypothesis `𝒯.IsBlockInvariant A`.

All `Γ`-bounds, on the window and on the slab, are near-pair bounds: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)} {α γ₀ η₀ η' η'' ζ : ℝ}
  {N N' : ℕ} {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N) (Ppoly : PolynomialSector 𝒯 N') (A : Finset ι)

include P Ppoly A hp

/-- **[Hai14, Thm. 7.8 (last statement), Prop. 9.8]: Lipschitz dependence of the `Φ⁴₃` fixed point
on `(v, Z)`.** See the module docstring. -/
theorem singularDiffBoundOn_phi4_fixedPoint_causal_win_near (hV : 𝒯.IsSector V)
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
      {CPi CGam CI CΓ R₀ T δ δv : ℝ}
      (v₁ : M₁.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T))
      (v₂ : M₂.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)),
      M₁.PiBoundOn (γ₀ + α + α) CPi hairerTimeWindow →
      M₂.PiBoundOn (γ₀ + α + α) CPi hairerTimeWindow →
      M₁.GammaNearOn (γ₀ + α + α) CGam hairerTimeWindow →
      M₂.GammaNearOn (γ₀ + α + α) CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₁.GrowthModel (γ₀ + α + α) C' C'' ρP ρG p q) →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₂.GrowthModel (γ₀ + α + α) C' C'' ρP ρG p q) → 0 ≤ CPi →
      M₁.IsRealisingP h (γ₀ + α + α) Ppoly I (blockSpan A) →
      M₂.IsRealisingP h (γ₀ + α + α) Ppoly I (blockSpan A) →
      IsAbstractIntegration Ppoly (blockSpan A) I 2 →
      (∀ a ∈ blockSpan A, ∀ kk : PolyIndex N', I a (Ppoly.emb kk) = 0) →
      (∀ i j, |I (Pi.single i 1) j| ≤ CI) → 0 ≤ CI →
      M₁.GammaNearOn γ₀ CΓ (timeSlab T) → M₁.GammaNearOn (γ₀ + α) CΓ (timeSlab T) →
      M₁.GammaNearOn (γ₀ + α + α + 2) CΓ (timeSlab T) →
      M₂.GammaNearOn γ₀ CΓ (timeSlab T) → M₂.GammaNearOn (γ₀ + α) CΓ (timeSlab T) →
      M₂.GammaNearOn (γ₀ + α + α + 2) CΓ (timeSlab T) → 0 ≤ CΓ →
      M₁.PiDiffBoundOn M₂ (γ₀ + α + α) δ hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ (γ₀ + α + α) δ hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ γ₀ δ (timeSlab T) → M₁.GammaDiffNearOn M₂ (γ₀ + α) δ (timeSlab T) →
      M₁.GammaDiffNearOn M₂ (γ₀ + α + α + 2) δ (timeSlab T) → 0 ≤ δ → 0 ≤ δv → 0 ≤ R₀ →
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
  obtain ⟨C₀, hC₀, h⟩ := singularDiffBoundOn_phi4_causalOperator_of_nonneg_win_near hp Ppoly A hγK hηK hηγ
    hAζ hζγ hζη hγpos hdeg hN hNγ hnat hni hVA
  refine ⟨C₀, hC₀, ?_⟩
  intro M₁ M₂ I CPi CGam CI CΓ R₀ T δ δv v₁ v₂ hPi₁ hPi₂ hGm₁ hGm₂ gr₁ gr₂ hCPi hreal₁ hreal₂
    hInt hIp hCI hCI0 hΓ₁₀ hΓ₁₁ hΓ₁K hΓ₂₀ hΓ₂₁ hΓ₂K hCΓ hdP hdG hdΓ₀ hdΓ₁ hdΓK hδ hδv hR₀ hT hT1
    hTT₀ 𝒦₁ 𝒦₂ h𝒦₁ h𝒦₂ hv U₁ U₂ hU₁ hU₂ hfix₁ hfix₂
  have hA₁ := gammaMap_blockProj_of_isBlockInvariant hAG M₁
  have hA₂ := gammaMap_blockProj_of_isBlockInvariant hAG M₂
  have hc := P.truncMulConst_nonneg
  have hK₂ : 0 ≤ (max 1 CGam * max CPi 1 +
      Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ := by positivity
  have hθ : 0 < (min (min ζ η'' + 2) γ₀ - η₀) / 2 := by
    have := lt_min hηK hηγ
    linarith
  refine singularDiffBoundOn_phi4_slab_fixedPoint_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
    hη''₁ hη''₂ hη''₃ hη''γ hΓ₁₀ hΓ₁₁ hΓ₂₀ hΓ₂₁ hdΓ₀ hdΓ₁ hCΓ hδ (C := C₀ * ((max 1 CGam * max CPi 1 +
      Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) * (1 + Fintype.card ι * CΓ))
    (by positivity) hθ hR₀ hT hTT₀ ?_ hδv 𝒦₁ 𝒦₂ ?_ hv hU₁ hU₂ hfix₁ hfix₂
  · positivity
  · intro g₁ g₂ b hg₁ hg₂ hb hd
    exact (h M₁ M₂ I hA₁ hA₂ g₁ g₂ hPi₁ hPi₂ hGm₁ hGm₂ gr₁ gr₂ hCPi hreal₁ hreal₂ hInt hIp hCI hCI0
      hΓ₁K hΓ₂K hCΓ hdP hdG hdΓK hδ hT hT1 hg₁ hg₂ hb hd).congr
      (fun x hx _ => (h𝒦₁ g₁ x hx).symm) (fun x hx _ => (h𝒦₂ g₂ x hx).symm)

end Model

end RegularityStructures

end
