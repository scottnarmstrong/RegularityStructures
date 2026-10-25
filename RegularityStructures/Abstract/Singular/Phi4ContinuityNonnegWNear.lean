/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.Singular.Diff.TruncationNear
public import RegularityStructures.Abstract.Singular.Phi4ContinuityNonnegNear
public import RegularityStructures.Abstract.Singular.Phi4ContinuityOperatorWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# Two-model bound for the `Φ⁴₃` operator, near-pair `Γ`-bounds

For two models at distance `δ ≥ 0` and inputs `g₁`, `g₂` with `‖gᵢ‖ ≤ B` whose difference satisfies
`SingularDiffBoundOn` with constant `b`, the outputs `Q_{<γ₀} 𝒦_γ` of their block projections
satisfy `SingularDiffBoundOn` with a constant of order `T^θ (b + δ B)`, for models whose `Γ`-bounds
hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- **The operator bound for `δ ≥ 0`**: `Model.singularDiffBoundOn_phi4_causalOperator_win_near`
with `0 ≤ δ`. -/
theorem singularDiffBoundOn_phi4_causalOperator_of_nonneg_win_near {γ₀ α η₀ η'' ζ : ℝ} {N N' : ℕ}
    {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N) (Ppoly : PolynomialSector 𝒯 N') (A : Finset ι)
    (hγK : γ₀ ≤ γ₀ + α + α + 2) (hηK : η₀ < min ζ η'' + 2) (hηγ : η₀ < γ₀)
    (hAζ : ∀ i ∈ A, ζ ≤ 𝒯.deg i) (hζγ : ζ ≤ γ₀ + α + α) (hζη : -2 < min ζ η'')
    (hγpos : 0 < γ₀ + α + α) (hdeg : ∀ j, 𝒯.deg j < γ₀ + α + α → -4 < 𝒯.deg j)
    (hN : N' ≤ N)
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ₀ + α + α + 2 → multiDeg l < N')
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ₀ + α + α + 2 - multiDeg k)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ i, i ∉ Set.range Ppoly.emb → ζ ≤ 𝒯.deg i → 𝒯.deg i < γ₀ + α + α → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (hVA : 𝒯.IsSector (blockSpan A)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (M₁ M₂ : Model 𝒯 parabolicSemigroup) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      {CPi CGam CI CΓ δ T B : ℝ}
      (hA₁ : ∀ x y τ, M₁.gammaMap x y (blockProj A τ) = blockProj A (M₁.gammaMap x y τ))
      (hA₂ : ∀ x y τ, M₂.gammaMap x y (blockProj A τ) = blockProj A (M₂.gammaMap x y τ))
      (g₁ : M₁.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T))
      (g₂ : M₂.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T)) {b : ℝ},
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
      M₁.GammaNearOn (γ₀ + α + α + 2) CΓ (timeSlab T) →
      M₂.GammaNearOn (γ₀ + α + α + 2) CΓ (timeSlab T) → 0 ≤ CΓ →
      M₁.PiDiffBoundOn M₂ (γ₀ + α + α) δ hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ (γ₀ + α + α) δ hairerTimeWindow →
      M₁.GammaDiffNearOn M₂ (γ₀ + α + α + 2) δ (timeSlab T) → 0 ≤ δ → 0 < T → T ≤ 1 →
      ‖g₁‖ ≤ B → ‖g₂‖ ≤ B → 0 ≤ b →
      M₁.SingularDiffBoundOn M₂ timeZeroDist (γ₀ + α + α) η'' b (timeSlab T) g₁.val g₂.val →
      M₁.SingularDiffBoundOn M₂ timeZeroDist γ₀ η₀
        (C₀ * ((max 1 CGam * max CPi 1 +
            Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
            (1 + Fintype.card ι * CΓ) * T ^ ((min (min ζ η'' + 2) γ₀ - η₀) / 2) * b +
          T ^ ((min (min ζ η'' + 2) γ₀ - η₀) / 2) * δ * B *
            (C₀ * ((max 1 CGam * max CPi 1 +
              Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
              (1 + Fintype.card ι * CΓ + Fintype.card ι))) (timeSlab T)
        (fun x => lowerProj 𝒯.deg γ₀
          (M₁.kGammaRemG h r Ppoly I (γ₀ + α + α) (SlabSpace.blockProj A hA₁ g₁).val x))
        (fun x => lowerProj 𝒯.deg γ₀
          (M₂.kGammaRemG h r Ppoly I (γ₀ + α + α) (SlabSpace.blockProj A hA₂ g₂).val x)) := by
  obtain ⟨C₀, hC₀, h⟩ := singularDiffBoundOn_phi4_causalOperator_win_near hp Ppoly A hγK hηK hηγ hAζ hζγ hζη
    hγpos hdeg hN hNγ hnat hni hVA
  refine ⟨C₀, hC₀, ?_⟩
  intro M₁ M₂ I CPi CGam CI CΓ δ T B hA₁ hA₂ g₁ g₂ b hPi₁ hPi₂ hGm₁ hGm₂ gr₁ gr₂ hCPi hreal₁ hreal₂ hInt hIp
    hCI hCI0 hΓ₁ hΓ₂ hCΓ hdP hdG hdG2 hδ hT hT1 hg₁ hg₂ hb hd
  rcases hδ.eq_or_lt with hδ0 | hδpos
  · subst hδ0
    refine SingularDiffBoundOn.of_forall_lt fun c' hc' => ?_
    set t := T ^ ((min (min ζ η'' + 2) γ₀ - η₀) / 2) with ht
    set Kc : ℝ := C₀ * ((max 1 CGam * max CPi 1 +
      Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
      (1 + Fintype.card ι * CΓ + Fintype.card ι) with hKc
    have ht0 : 0 ≤ t := Real.rpow_nonneg hT.le _
    have hB0 : 0 ≤ B := (norm_nonneg g₁).trans hg₁
    have hKc0 : 0 ≤ Kc := by positivity
    set δ' : ℝ := (c' - (C₀ * ((max 1 CGam * max CPi 1 +
      Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
      (1 + Fintype.card ι * CΓ) * t * b + t * 0 * B * Kc)) / (t * B * Kc + 1) with hδ'
    have hpos : 0 < c' - (C₀ * ((max 1 CGam * max CPi 1 +
      Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
      (1 + Fintype.card ι * CΓ) * t * b + t * 0 * B * Kc) := sub_pos.2 hc'
    have hδ'0 : 0 < δ' := div_pos hpos (by positivity)
    have h' := h M₁ M₂ I hA₁ hA₂ g₁ g₂ hPi₁ hPi₂ hGm₁ hGm₂ gr₁ gr₂ hCPi hreal₁ hreal₂ hInt hIp hCI hCI0
      hΓ₁ hΓ₂ hCΓ (piDiffBoundOn_mono hdP hδ'0.le)
      (gammaDiffBoundOn_mono_near hdG hδ'0.le)
      (gammaDiffBoundOn_mono_near hdG2 hδ'0.le) hδ'0 hT hT1 hg₁ hg₂ hb hd
    refine h'.mono ?_
    have : t * δ' * B * Kc ≤ c' - (C₀ * ((max 1 CGam * max CPi 1 +
      Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
      (1 + Fintype.card ι * CΓ) * t * b + t * 0 * B * Kc) := by
      have e : t * δ' * B * Kc = δ' * (t * B * Kc) := by ring
      rw [e, hδ', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  · exact h M₁ M₂ I hA₁ hA₂ g₁ g₂ hPi₁ hPi₂ hGm₁ hGm₂ gr₁ gr₂ hCPi hreal₁ hreal₂ hInt hIp hCI hCI0
      hΓ₁ hΓ₂ hCΓ hdP hdG hdG2 hδpos hT hT1 hg₁ hg₂ hb hd

end Model

end RegularityStructures

end
