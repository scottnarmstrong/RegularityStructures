/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Phi4ContinuityWinNearOne
public import Phi43.TimeSlice.AbstractOne
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.BlockInvariant
public import RegularityStructures.Abstract.Singular.Diff.BlockProj
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# One-coefficient difference bound for the integration operator applied to cubes

Two-model version of `Phi43.TimeSlice.exists_abs_kernel_cube_apply_le`: for models `M₁, M₂` with
`δ`-close `Π`- and `Γ`-bounds, operators `𝒦₁, 𝒦₂` with the characterisation clause and slab
elements `U₁, U₂` with `‖Uᵢ‖ ≤ R₀ + 1` and `|||U₁; U₂||| ≤ δU`, the coefficients with
`deg i < γ₀` of `𝒦₁ (U₁³) − 𝒦₂ (U₂³)` are bounded by a constant times `(δU + δ)` and the weight
`singularWeight timeZeroDist x ^ (min ζ η'' + 2 - deg i)`.
-/

public section

namespace RegularityStructures.Phi43.TimeSlice

open RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

private theorem piDiffBoundOn_mono {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
    {K : RegularisingSemigroup E μ} {M₁ M₂ : Model 𝒯 K} {γ C C' : ℝ} {S : Set E}
    (h : M₁.PiDiffBoundOn M₂ γ C S) (hC : C ≤ C') : M₁.PiDiffBoundOn M₂ γ C' S :=
  fun i hi t ht x hx => (h i hi t ht x hx).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.1.le _))

private theorem delta_arith {q R δU δ' C₁ b : ℝ} (hq : 0 ≤ q) (hR : 1 ≤ R) (hδU : 0 ≤ δU)
    (hδ' : 0 ≤ δ') (hC₁ : C₁ ≤ q * R ^ 3) (hb : b = q * (3 * R ^ 2 * δU + 4 * R ^ 3 * δ')) :
    δ' * C₁ + b ≤ q * 5 * R ^ 3 * (δU + δ') := by
  have h2 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have h3 : 0 ≤ R ^ 3 := by positivity
  have e1 : δ' * C₁ ≤ δ' * (q * R ^ 3) := mul_le_mul_of_nonneg_left hC₁ hδ'
  have e2 : 3 * R ^ 2 * δU ≤ 3 * R ^ 3 * δU :=
    mul_le_mul_of_nonneg_right (by linarith) hδU
  have e3 : q * (3 * R ^ 2 * δU + 4 * R ^ 3 * δ') ≤ q * (3 * R ^ 3 * δU + 4 * R ^ 3 * δ') :=
    mul_le_mul_of_nonneg_left (by linarith) hq
  have e4 : 0 ≤ q * (R ^ 3 * δU) := by positivity
  rw [hb]
  nlinarith [e1, e3, e4]

private theorem le_of_forall_pos_mul_add {d A L : ℝ} (hL : 0 ≤ L)
    (h : ∀ ε : ℝ, 0 < ε → d ≤ A + ε * L) : d ≤ A := by
  refine le_of_forall_pos_le_add fun ε' hε' => ?_
  have hpos : 0 < L + 1 := by linarith
  have := h (ε' / (L + 1)) (div_pos hε' hpos)
  have h2 : ε' / (L + 1) * L ≤ ε' := by
    calc ε' / (L + 1) * L ≤ ε' / (L + 1) * (L + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_pos hε' hpos).le
      _ = ε' := div_mul_cancel₀ _ hpos.ne'
  linarith

/-- **One-coefficient difference bound for `𝒦₁ (U₁³) − 𝒦₂ (U₂³)`** (near-`1` `Γ`-hypotheses). -/
theorem exists_abs_kernel_cube_sub_apply_le (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)}
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
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (M₁ M₂ : Model 𝒯 parabolicSemigroup) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      {CPi CGam CI CΓ CGam₁ CΓ₁ δ₁ R₀ T δ δU : ℝ},
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
      gammaDiffChainConst (Fintype.card ι) CΓ₁ δ₁ 16 ≤ δ → 0 ≤ δ → 0 ≤ δU → 0 ≤ R₀ →
      T ≤ 1 →
      ∀ (𝒦₁ : M₁.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) →ₗ[ℝ]
          M₁.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T))
        (𝒦₂ : M₂.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) →ₗ[ℝ]
          M₂.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)),
      (∀ g, ∀ x ∈ timeSlab T, (𝒦₁ g).val x = lowerProj 𝒯.deg γ₀
        (M₁.kGammaRemG h r Ppoly I (γ₀ + α + α)
          (Model.SlabSpace.blockProj A (Model.gammaMap_blockProj_of_isBlockInvariant hAG M₁)
            g).val x)) →
      (∀ g, ∀ x ∈ timeSlab T, (𝒦₂ g).val x = lowerProj 𝒯.deg γ₀
        (M₂.kGammaRemG h r Ppoly I (γ₀ + α + α)
          (Model.SlabSpace.blockProj A (Model.gammaMap_blockProj_of_isBlockInvariant hAG M₂)
            g).val x)) →
      ∀ (U₁ : M₁.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T))
        (U₂ : M₂.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)),
      ‖U₁‖ ≤ R₀ + 1 → ‖U₂‖ ≤ R₀ + 1 →
      M₁.SingularDiffBoundOn M₂ timeZeroDist γ₀ η₀ δU (timeSlab T) U₁.val U₂.val →
      ∀ x ∈ timeSlab T, ∀ i, 𝒯.deg i < γ₀ →
        |(𝒦₁ (Model.SlabSpace.cube P (γ₀ + α + α) η'' U₁)).val x i -
            (𝒦₂ (Model.SlabSpace.cube P (γ₀ + α + α) η'' U₂)).val x i| ≤
          C₀ * (((max 1 CGam * max CPi 1 +
            Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) *
            (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * 5)) * (R₀ + 1) ^ 3 * (δU + δ) *
            singularWeight timeZeroDist x ^ (min ζ η'' + 2 - 𝒯.deg i) := by
  classical
  obtain ⟨Ca, hCa, hspec2⟩ := Model.exists_singularDiffBoundOn_kGammaRemG_of_le_win_near
    (γ₀ + α + α) η'' ζ N Ppoly hp hγpos hdeg hζγ hζη hN hNγ hnat hni hVA (isCoordClosed_blockSpan A)
    (fun i hi => hAζ i (mem_of_single_mem_blockSpan hi))
  refine ⟨Ca, hCa, ?_⟩
  intro M₁ M₂ I CPi CGam CI CΓ CGam₁ CΓ₁ δ₁ R₀ T δ δU hPi₁ hPi₂ hG₁ hG₂ hCG gr₁ gr₂ hCPi hreal₁
    hreal₂ hInt hIp hCI hCI0 hΓ₁₀ hΓ₁₁ hΓ₁K hΓ₂₀ hΓ₂₁ hΓ₂K hCΓr hCΓ hdP hdG hdGr hdΓ₀ hdΓ₁ hdΓK
    hdΓr hδ hδU hR₀ hT1 𝒦₁ 𝒦₂ h𝒦₁ h𝒦₂ U₁ U₂ hU₁ hU₂ hUd x hx i hi
  have hSW := segmentClosed_hairerTimeWindow
  have hS := segmentClosed_timeSlab T
  have hGm₁ := (hG₁.toGammaNearOn M₁ hSW).mono M₁ hCG
  have hGm₂ := (hG₂.toGammaNearOn M₂ hSW).mono M₂ hCG
  have hΓ₁₀' := (hΓ₁₀.toGammaNearOn M₁ hS).mono M₁ hCΓr
  have hΓ₁₁' := (hΓ₁₁.toGammaNearOn M₁ hS).mono M₁ hCΓr
  have hΓ₁K' := (hΓ₁K.toGammaNearOn M₁ hS).mono M₁ hCΓr
  have hΓ₂₀' := (hΓ₂₀.toGammaNearOn M₂ hS).mono M₂ hCΓr
  have hΓ₂₁' := (hΓ₂₁.toGammaNearOn M₂ hS).mono M₂ hCΓr
  have hΓ₂K' := (hΓ₂K.toGammaNearOn M₂ hS).mono M₂ hCΓr
  have hA₁ := Model.gammaMap_blockProj_of_isBlockInvariant hAG M₁
  have hA₂ := Model.gammaMap_blockProj_of_isBlockInvariant hAG M₂
  set g₁ := Model.SlabSpace.cube P (γ₀ + α + α) η'' U₁ with hg₁
  set g₂ := Model.SlabSpace.cube P (γ₀ + α + α) η'' U₂ with hg₂
  have hS₁ := Model.layerSettingW_blockProj_near A hA₁ g₁ hγpos hPi₁ hCPi hGm₁ gr₁ hT1 hdeg hAζ
    hζγ hζη
  have hS₂ := Model.layerSettingW_blockProj_near A hA₂ g₂ hγpos hPi₂ hCPi hGm₂ gr₂ hT1 hdeg hAζ
    hζγ hζη
  have hfA₁ : ∀ z, (Model.SlabSpace.blockProj A hA₁ g₁).val z ∈ blockSpan A := fun z =>
    mem_blockSpan_of_forall fun i hi => by
      rw [Model.SlabSpace.val_blockProj]
      exact blockProj_apply_of_notMem hi _
  have hfA₂ : ∀ z, (Model.SlabSpace.blockProj A hA₂ g₂).val z ∈ blockSpan A := fun z =>
    mem_blockSpan_of_forall fun i hi => by
      rw [Model.SlabSpace.val_blockProj]
      exact blockProj_apply_of_notMem hi _
  have hq : 0 ≤ P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 := by
    have := P.truncMulConst_nonneg
    positivity
  have hR1 : (1 : ℝ) ≤ R₀ + 1 := by linarith
  have hcube : ∀ (M' : Model 𝒯 parabolicSemigroup) (u : M'.SlabSpace timeZeroDist V γ₀ η₀
      (timeSlab T)), M'.GammaNearOn γ₀ CΓ (timeSlab T) → M'.GammaNearOn (γ₀ + α) CΓ (timeSlab T) →
      ‖u‖ ≤ R₀ + 1 →
      ‖Model.SlabSpace.cube P (γ₀ + α + α) η'' u‖ ≤
        (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) * (R₀ + 1) ^ 3 := by
    intro M' u h₀ h₁ hu
    refine (Model.SlabSpace.norm_cube_le_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
      hη''₁ hη''₂ hη''₃ hη''γ u h₀ h₁ hCΓ).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg u) hu 3
    calc P.truncMulConst ^ 2 * ‖u‖ ^ 3 * (1 + CΓ) ^ 4
        = (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) * ‖u‖ ^ 3 := by ring
      _ ≤ _ := by gcongr
  have hC₁ : ‖Model.SlabSpace.blockProj A hA₁ g₁‖ ≤
      (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) * (R₀ + 1) ^ 3 :=
    (Model.SlabSpace.norm_blockProj_le A hA₁ g₁).trans (hcube M₁ U₁ hΓ₁₀' hΓ₁₁' hU₁)
  have hn : (Fintype.card ι : ℝ) ≤ Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) := by
    rw [Fintype.card_sum]
    exact_mod_cast Nat.le_add_left _ _
  have hn0 : (0 : ℝ) ≤ Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) :=
    (Nat.cast_nonneg _)
  have hKc : 0 ≤ (max 1 CGam * max CPi 1 +
      Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ := by
    have h1 : 0 ≤ max 1 CGam := zero_le_one.trans (le_max_left _ _)
    have h2 : 0 ≤ max CPi 1 := zero_le_one.trans (le_max_right _ _)
    have h3 : 0 ≤ max 1 CΓ := zero_le_one.trans (le_max_left _ _)
    positivity
  have hw : 0 ≤ singularWeight timeZeroDist x ^ (min ζ η'' + 2 - 𝒯.deg i) :=
    Real.rpow_nonneg (Layer.singularWeight_nonneg x) _
  have main : ∀ ε : ℝ, 0 < ε →
      |(𝒦₁ g₁).val x i - (𝒦₂ g₂).val x i| ≤
        Ca * (((max 1 CGam * max CPi 1 + Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) *
          max 1 CΓ) * (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * 5)) * (R₀ + 1) ^ 3 *
          (δU + δ + ε) * singularWeight timeZeroDist x ^ (min ζ η'' + 2 - 𝒯.deg i) := by
    intro ε hε
    set δ' := δ + ε with hδ'
    have hδδ' : δ ≤ δ' := by linarith
    have hδ'0 : 0 < δ' := by linarith
    have dP := piDiffBoundOn_mono hdP hδδ'
    have dW := (Model.GammaDiffBoundNearOn.toGammaDiffNearOn hSW hG₁ hG₂ hdG).mono_const
      (hdGr.trans hδδ')
    have d₀ := (Model.GammaDiffBoundNearOn.toGammaDiffNearOn hS hΓ₁₀ hΓ₂₀ hdΓ₀).mono_const
      (hdΓr.trans hδδ')
    have d₁ := (Model.GammaDiffBoundNearOn.toGammaDiffNearOn hS hΓ₁₁ hΓ₂₁ hdΓ₁).mono_const
      (hdΓr.trans hδδ')
    have dK := (Model.GammaDiffBoundNearOn.toGammaDiffNearOn hS hΓ₁K hΓ₂K hdΓK).mono_const
      (hdΓr.trans hδδ')
    have hd := Model.singularDiffBoundOn_truncCube_near M₁ M₂ P hV hW hVα hWα hVVW hreg₁ hreg₂
      hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ
      (fun x hx hρ => (Submodule.mem_inf.1 (U₁.mem_inf hx hρ)).1)
      (fun x hx hρ => (Submodule.mem_inf.1 (U₂.mem_inf hx hρ)).1)
      (fun x hx hρ => (Submodule.mem_inf.1 (U₁.mem_inf hx hρ)).2)
      (fun x hx hρ => (Submodule.mem_inf.1 (U₂.mem_inf hx hρ)).2)
      (U₁.singularBoundOn_norm.mono M₁ hU₁) (U₂.singularBoundOn_norm.mono M₂ hU₂) hUd
      (by linarith) hδU hΓ₁₀' hΓ₁₁' hΓ₂₀' hΓ₂₁' d₀ d₁ hCΓ hδ'0.le
    rw [← Model.SlabSpace.val_cube_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁
      hη''₂ hη''₃ hη''γ U₁ hΓ₁₀' hΓ₁₁' hCΓ, ← Model.SlabSpace.val_cube_near P hV hW hVα hWα hVVW
      hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ U₂ hΓ₂₀' hΓ₂₁' hCΓ] at hd
    have hfd := Model.SingularDiffBoundOn.blockProj hA₁ hA₂ hd
    have hb0 : 0 ≤ P.truncMulConst ^ 2 * (3 * (R₀ + 1) ^ 2 * δU + 4 * (R₀ + 1) ^ 3 * δ') *
        (1 + CΓ) ^ 4 := by
      have := P.truncMulConst_nonneg
      positivity
    obtain ⟨-, hFpt⟩ := hspec2 M₁ M₂ (Model.SlabSpace.blockProj A hA₁ g₁).val
      (Model.SlabSpace.blockProj A hA₂ g₂).val T ‖Model.SlabSpace.blockProj A hA₁ g₁‖
      ‖Model.SlabSpace.blockProj A hA₂ g₂‖ _ CPi CPi CGam CGam δ' δ' δ' CI CΓ CΓ δ' I hδ'0
      le_rfl le_rfl le_rfl hS₁ hS₂ hreal₁ hreal₂ hInt hIp hCI hCI0 hb0 hfA₁ hfA₂ dP dW
      hΓ₁K' hΓ₂K' dK hfd
    simp only [max_self] at hFpt
    rw [h𝒦₁ g₁ x hx, h𝒦₂ g₂ x hx, lowerProj_apply_of_lt hi, lowerProj_apply_of_lt hi]
    refine (hFpt x hx i (hi.trans_le hγK)).trans ?_
    have hineq := delta_arith hq hR1 hδU hδ'0.le hC₁
      (b := P.truncMulConst ^ 2 * (3 * (R₀ + 1) ^ 2 * δU + 4 * (R₀ + 1) ^ 3 * δ') *
        (1 + CΓ) ^ 4) (by ring)
    have hCaK : 0 ≤ Ca * ((max 1 CGam * max CPi 1 +
        Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) * max 1 CΓ) := mul_nonneg hCa hKc
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hineq hCaK) hw
    refine this.trans (le_of_eq ?_)
    simp only [hδ']
    ring
  set L := Ca * (((max 1 CGam * max CPi 1 + Fintype.card (TwoModel.NonPoly Ppoly ⊕ ι) * CI) *
      max 1 CΓ) * (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * 5)) * (R₀ + 1) ^ 3 *
      singularWeight timeZeroDist x ^ (min ζ η'' + 2 - 𝒯.deg i) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    have : 0 ≤ (R₀ + 1) ^ 3 := by positivity
    have h5 : 0 ≤ P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * 5 := by positivity
    positivity
  have hfinal : |(𝒦₁ g₁).val x i - (𝒦₂ g₂).val x i| ≤ L * (δU + δ) := by
    refine le_of_forall_pos_mul_add hL0 fun ε hε => ?_
    refine (main ε hε).trans (le_of_eq ?_)
    rw [hL]
    ring
  refine hfinal.trans (le_of_eq ?_)
  rw [hL]
  ring

end RegularityStructures.Phi43.TimeSlice

end
