/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.Singular.Diff.TruncationNear
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlockWNear
public import RegularityStructures.Abstract.Singular.Theorem71.MainWNear
public import RegularityStructures.Abstract.Singular.TwoModel.CorollaryWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.Diff.BlockProj
public import RegularityStructures.Abstract.Singular.Diff.ShortTime
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# Lipschitz dependence of the `Φ⁴₃` integration operator on the model, near-pair `Γ`-bounds

`singularDiffBoundOn_phi4_causalOperator_win_near`: the `Φ⁴₃` integration operator built from a
kernel pair `(h, r)` is Lipschitz in the model, by the two-model form of Theorem 7.1, the two-model
truncation and the short-time gain. Both models have model bounds on `hairerTimeWindow` and a
qualitative growth model, the model difference is controlled by `PiDiffBoundOn` and
`GammaDiffNearOn` on `hairerTimeWindow`, and the constants involve `max 1 CGam * max CPi 1` and no
weights.

This is the version for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- **The `Φ⁴₃` integration operator is Lipschitz in the model** (two-model Theorem 7.1 + two-model
truncation + short-time gain). -/
theorem singularDiffBoundOn_phi4_causalOperator_win_near {γ₀ α η₀ η'' ζ : ℝ} {N N' : ℕ}
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
      M₁.GammaDiffNearOn M₂ (γ₀ + α + α + 2) δ (timeSlab T) → 0 < δ → 0 < T → T ≤ 1 →
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
  obtain ⟨Ca, hCa, hspec2⟩ := exists_singularDiffBoundOn_kGammaRemG_of_le_win_near (γ₀ + α + α) η'' ζ N
    Ppoly hp hγpos hdeg hζγ hζη hN hNγ hnat hni hVA (isCoordClosed_blockSpan A)
    (fun i hi => hAζ i (mem_of_single_mem_blockSpan hi))
  obtain ⟨Cb, hCb, hspec1⟩ := exists_singularBoundOn_kGammaRemG_win_near (γ₀ + α + α) η'' ζ N Ppoly hp hγpos
    hdeg hζγ hζη hN hNγ hnat hni hVA (isCoordClosed_blockSpan A)
    (fun i hi => hAζ i (mem_of_single_mem_blockSpan hi))
  refine ⟨Ca + Cb, add_nonneg hCa hCb, ?_⟩
  intro M₁ M₂ I CPi CGam CI CΓ δ T B hA₁ hA₂ g₁ g₂ b hPi₁ hPi₂ hGm₁ hGm₂ gr₁ gr₂ hCPi hreal₁ hreal₂ hInt hIp
    hCI hCI0 hΓ₁ hΓ₂ hCΓ hdP hdG hdG2 hδ hT hT1 hg₁ hg₂ hb hd
  classical
  have hS₁ := layerSettingW_blockProj_near A hA₁ g₁ hγpos hPi₁ hCPi hGm₁ gr₁ hT1 hdeg hAζ hζγ hζη
  have hS₂ := layerSettingW_blockProj_near A hA₂ g₂ hγpos hPi₂ hCPi hGm₂ gr₂ hT1 hdeg hAζ hζγ hζη
  have hfA₁ : ∀ z, (SlabSpace.blockProj A hA₁ g₁).val z ∈ blockSpan A := fun z =>
    mem_blockSpan_of_forall fun i hi => by
      rw [SlabSpace.val_blockProj]
      exact blockProj_apply_of_notMem hi _
  have hfA₂ : ∀ z, (SlabSpace.blockProj A hA₂ g₂).val z ∈ blockSpan A := fun z =>
    mem_blockSpan_of_forall fun i hi => by
      rw [SlabSpace.val_blockProj]
      exact blockProj_apply_of_notMem hi _
  have hfd : M₁.SingularDiffBoundOn M₂ timeZeroDist (γ₀ + α + α) η'' b (timeSlab T)
      (SlabSpace.blockProj A hA₁ g₁).val (SlabSpace.blockProj A hA₂ g₂).val :=
    SingularDiffBoundOn.blockProj hA₁ hA₂ hd
  obtain ⟨hF, hFpt⟩ := hspec2 M₁ M₂ (SlabSpace.blockProj A hA₁ g₁).val
    (SlabSpace.blockProj A hA₂ g₂).val T ‖SlabSpace.blockProj A hA₁ g₁‖
    ‖SlabSpace.blockProj A hA₂ g₂‖ b CPi CPi CGam CGam δ δ δ CI CΓ CΓ δ I hδ le_rfl le_rfl le_rfl
    hS₁ hS₂ hreal₁ hreal₂ hInt hIp hCI hCI0 hb hfA₁ hfA₂ hdP hdG hΓ₁ hΓ₂ hdG2 hfd
  simp only [max_self] at hF hFpt
  obtain ⟨hf₁T, hf₁, -⟩ := hspec1 M₁ (SlabSpace.blockProj A hA₁ g₁).val T
    ‖SlabSpace.blockProj A hA₁ g₁‖ CPi CGam CI CΓ I hS₁ hreal₁ hInt hIp hCI hfA₁ hΓ₁
  obtain ⟨hf₂T, -, -⟩ := hspec1 M₂ (SlabSpace.blockProj A hA₂ g₂).val T
    ‖SlabSpace.blockProj A hA₂ g₂‖ CPi CGam CI CΓ I hS₂ hreal₂ hInt hIp hCI hfA₂ hΓ₂
  have hc₁ : ‖SlabSpace.blockProj A hA₁ g₁‖ ≤ B := (SlabSpace.norm_blockProj_le A hA₁ g₁).trans hg₁
  have hc₁0 : 0 ≤ ‖SlabSpace.blockProj A hA₁ g₁‖ := norm_nonneg _
  set c₁ := ‖SlabSpace.blockProj A hA₁ g₁‖ with hc₁def
  have hn : (Fintype.card ι : ℝ) ≤ Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) := by
    rw [Fintype.card_sum]
    exact_mod_cast Nat.le_add_left _ _
  have hn0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hCI1 : (0 : ℝ) ≤ Fintype.card ι * CI := mul_nonneg hn0 hCI0
  have hK₁ : 0 ≤ (max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ := by positivity
  have hK₂ : 0 ≤ (max 1 CGam * max CPi 1 + Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) *
      max 1 CΓ := by positivity
  have hK₁₂ : (max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ ≤
      (max 1 CGam * max CPi 1 + Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ := by
    have h1 : 0 ≤ max 1 CGam := zero_le_one.trans (le_max_left _ _)
    gcongr
    · exact le_max_left _ _
  set K₁ := (max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ with hK₁def
  set K₂ := (max 1 CGam * max CPi 1 + Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) *
    max 1 CΓ with hK₂def
  set n : ℝ := (Fintype.card ι : ℝ) with hndef
  set Dc : ℝ := Ca * K₂ * (δ * c₁ + b) with hDc
  have hDc0 : 0 ≤ Dc := by positivity
  have hC₁0 : 0 ≤ Cb * K₁ * c₁ := by positivity
  have hlow := SingularDiffBoundOn.lowerProj_near (γ := γ₀) hF hf₁ (fun x hx _ => hf₁T x hx)
    (fun x hx _ => hf₂T x hx) hγK hΓ₂ hdG2 hDc0 hC₁0 hCΓ hδ.le
  set C'' : ℝ := Dc * (1 + n * CΓ) + Cb * K₁ * c₁ * n * δ with hC''
  have hC''0 : 0 ≤ C'' := by positivity
  have hκ : 0 ≤ min (min ζ η'' + 2) γ₀ - η₀ := sub_nonneg.2 (le_min hηK.le hηγ.le)
  have hDC : Dc ≤ C'' := by
    have : 0 ≤ Cb * K₁ * c₁ * n * δ := by positivity
    have h2 : Dc ≤ Dc * (1 + n * CΓ) := by
      have : 0 ≤ Dc * (n * CΓ) := by positivity
      linarith
    linarith
  have hsup : ∀ x ∈ timeSlab T, 0 < timeZeroDist x → ∀ i, 𝒯.deg i < γ₀ →
      |lowerProj 𝒯.deg γ₀ (M₁.kGammaRemG h r Ppoly I (γ₀ + α + α)
          (SlabSpace.blockProj A hA₁ g₁).val x) i -
        lowerProj 𝒯.deg γ₀ (M₂.kGammaRemG h r Ppoly I (γ₀ + α + α)
          (SlabSpace.blockProj A hA₂ g₂).val x) i| ≤
        C'' * singularWeight timeZeroDist x ^
          (η₀ + (min (min ζ η'' + 2) γ₀ - η₀) - 𝒯.deg i) := by
    intro x hx hρ i hi
    rw [lowerProj_apply_of_lt hi, lowerProj_apply_of_lt hi]
    refine (hFpt x hx i (hi.trans_le hγK)).trans ?_
    have hw0 := singularWeight_pos hρ
    have hexp : η₀ + (min (min ζ η'' + 2) γ₀ - η₀) - 𝒯.deg i ≤ min ζ η'' + 2 - 𝒯.deg i := by
      linarith [min_le_left (min ζ η'' + 2) γ₀]
    exact mul_le_mul hDC (Real.rpow_le_rpow_of_exponent_ge hw0 (singularWeight_le_one _ x) hexp)
      (Real.rpow_nonneg hw0.le _) hC''0
  have hres := singularDiffBoundOn_timeSlab M₁ M₂ hκ hC''0 hT.le hsup
    (by rw [add_sub_cancel]; exact hlow)
  refine hres.mono ?_
  have ht : 0 ≤ T ^ ((min (min ζ η'' + 2) γ₀ - η₀) / 2) := Real.rpow_nonneg hT.le _
  have hCab : Ca ≤ Ca + Cb := le_add_of_nonneg_right hCb
  have hCbb : Cb ≤ Ca + Cb := le_add_of_nonneg_left hCa
  have h1 : C'' ≤ (Ca + Cb) * K₂ * (1 + n * CΓ) * b +
      δ * B * ((Ca + Cb) * K₂ * (1 + n * CΓ + n)) := by
    have hB0 : 0 ≤ B := hc₁0.trans hc₁
    have e1 : Dc * (1 + n * CΓ) ≤ (Ca + Cb) * K₂ * (δ * B + b) * (1 + n * CΓ) := by
      have : δ * c₁ ≤ δ * B := mul_le_mul_of_nonneg_left hc₁ hδ.le
      have h3 : Ca * K₂ ≤ (Ca + Cb) * K₂ := mul_le_mul_of_nonneg_right hCab hK₂
      have h4 : 0 ≤ Ca * K₂ := mul_nonneg hCa hK₂
      have h5 : Ca * K₂ * (δ * c₁ + b) ≤ (Ca + Cb) * K₂ * (δ * B + b) :=
        mul_le_mul h3 (by linarith) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right h5 (by positivity)
    have e2 : Cb * K₁ * c₁ * n * δ ≤ (Ca + Cb) * K₂ * B * n * δ := by
      have h3 : Cb * K₁ ≤ (Ca + Cb) * K₂ :=
        mul_le_mul hCbb hK₁₂ hK₁ (by positivity)
      have h4 : Cb * K₁ * c₁ ≤ (Ca + Cb) * K₂ * B :=
        mul_le_mul h3 hc₁ hc₁0 (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hn0) hδ.le
    calc C'' ≤ (Ca + Cb) * K₂ * (δ * B + b) * (1 + n * CΓ) +
          (Ca + Cb) * K₂ * B * n * δ := add_le_add e1 e2
      _ = _ := by ring
  calc T ^ ((min (min ζ η'' + 2) γ₀ - η₀) / 2) * C''
      ≤ T ^ ((min (min ζ η'' + 2) γ₀ - η₀) / 2) * ((Ca + Cb) * K₂ * (1 + n * CΓ) * b +
      δ * B * ((Ca + Cb) * K₂ * (1 + n * CΓ + n))) := mul_le_mul_of_nonneg_left h1 ht
    _ = _ := by ring

end Model

end RegularityStructures

end
