/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTruncationNear
public import RegularityStructures.Abstract.Singular.FixedPointBlockNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlockWNear
public import RegularityStructures.Abstract.Singular.Phi4FixedPointOperatorWNear
public import RegularityStructures.Abstract.Singular.Slab.TimeSlabOperatorNear
public import RegularityStructures.Abstract.Singular.Theorem71.MainWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.BlockInvariant
public import RegularityStructures.Abstract.Singular.Phi4FixedPointOperatorWeighted
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Singular.Window.Basic

/-!
# The abstract `Φ⁴₃` fixed point on a short time slab, near-pair `Γ`-bounds

[Hai14, Thm. 7.1, Thm. 7.8, Prop. 9.8 (local part)]: under window model bounds and for a
block-invariant sector `blockSpan A`, the operator `g ↦ Q_{<γ₀} 𝒦_γ` applied to the block projection
of `g` (built from `kGammaRemG`) is a linear map between slab spaces, and for `T` below an explicit
`fixedPointTime` the equation `U = −𝒦(U³) + v` has a unique solution with `|||U||| ≤ R₀ + 1`, for
models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)} {α γ₀ η₀ η' η'' ζ : ℝ}
  {N N' : ℕ} {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N)
  (Ppoly : PolynomialSector 𝒯 N') (A : Finset ι)

include P Ppoly A hp

/-- **The abstract `Φ⁴₃` fixed point on a short time slab, window model bounds and structural
block invariance** [Hai14, Thm. 7.1, Thm. 7.8, Prop. 9.8 (local part)]. See the module docstring. -/
theorem exists_unique_phi4_fixedPoint_causal_win_near (hV : 𝒯.IsSector V)
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
      {CPi CGam CI CΓ R₀ T : ℝ} (v : M.SlabSpace timeZeroDist V γ₀ η₀ (timeSlab T)),
      M.PiBoundOn (γ₀ + α + α) CPi hairerTimeWindow →
      M.GammaNearOn (γ₀ + α + α) CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M.GrowthModel (γ₀ + α + α) C' C'' ρP ρG p q) → 0 ≤ CPi → M.IsJointMeasurable →
      M.IsRealisingP h (γ₀ + α + α) Ppoly I (blockSpan A) →
      IsAbstractIntegration Ppoly (blockSpan A) I 2 →
      (∀ a ∈ blockSpan A, ∀ kk : PolyIndex N', I a (Ppoly.emb kk) = 0) →
      (∀ i j, |I (Pi.single i 1) j| ≤ CI) →
      (∀ a ∈ blockSpan A, I a ∈ V) →
      M.GammaNearOn γ₀ CΓ (timeSlab T) → M.GammaNearOn (γ₀ + α) CΓ (timeSlab T) →
      M.GammaNearOn (γ₀ + α + α + 2) CΓ (timeSlab T) → 0 ≤ CΓ → 0 ≤ R₀ →
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
  obtain ⟨C₀, hC₀, hspec⟩ := exists_singularBoundOn_kGammaRemG_win_near (γ₀ + α + α) η'' ζ N Ppoly hp hγpos
    hdeg hζγ hζη hN hNγ hnat hni hVA (isCoordClosed_blockSpan A)
    (fun i hi => hAζ i (mem_of_single_mem_blockSpan hi))
  refine ⟨C₀, hC₀, fun M I CPi CGam CI CΓ R₀ T v hPi hGam hgr hCPi hJ hreal hInt hIp hCI hIV hΓ₀
    hΓ₁ hΓK hCΓ hR₀ hT hT1 hTT₀ hv => ?_⟩
  have hA := gammaMap_blockProj_of_isBlockInvariant hAG M
  have hK₁ : 0 ≤ (max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ := by
    have hcI : 0 ≤ (Fintype.card ι : ℝ) * CI := by
      rcases isEmpty_or_nonempty ι with he | ⟨⟨i⟩⟩
      · simp [Fintype.card_eq_zero]
      · exact mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans (hCI i i))
    exact mul_nonneg (add_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi) hcI)
      (zero_le_one.trans (le_max_left _ _))
  have hC : 0 ≤ C₀ * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ) :=
    mul_nonneg hC₀ hK₁
  have hS : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      LayerSettingWNear M (SlabSpace.blockProj A hA g).val (γ₀ + α + α) η'' ζ
        ‖SlabSpace.blockProj A hA g‖ CPi CGam T := fun g =>
    layerSettingW_blockProj_near A hA g hγpos hPi hCPi hGam hgr hT1 hdeg hAζ hζγ hζη
  have hfA : ∀ (g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T)) z,
      (SlabSpace.blockProj A hA g).val z ∈ blockSpan A := fun g z =>
    mem_blockSpan_of_forall fun i hi => by
      rw [SlabSpace.val_blockProj]
      exact blockProj_apply_of_notMem hi _
  have hsp := fun g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T) =>
    hspec M (SlabSpace.blockProj A hA g).val T ‖SlabSpace.blockProj A hA g‖ CPi CGam CI CΓ I
      (hS g) hreal hInt hIp hCI (hfA g) hΓK
  have hFadd : ∀ g g' : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T (SlabSpace.blockProj A hA (g + g')).val =
        M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T (SlabSpace.blockProj A hA g).val +
        M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T (SlabSpace.blockProj A hA g').val :=
    fun g g' => by
      rw [map_add, SlabSpace.val_add]
      exact kGammaRemGSlab_add_win_near hp (hS g) (hS g') hN hreal.poly hni I
  have hFsmul : ∀ (c : ℝ) (g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T)),
      M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T (SlabSpace.blockProj A hA (c • g)).val =
        c • M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T (SlabSpace.blockProj A hA g).val :=
    fun c g => by
      rw [map_smul, SlabSpace.val_smul]
      exact kGammaRemGSlab_smul_win_near hp (hS g) c I
  have hFmeas : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      Measurable ((timeSlab T).indicator (M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T
        (SlabSpace.blockProj A hA g).val)) := fun g => by
    have hm := measurable_kGammaRemGSlab_win_near (P := Ppoly) hp (hS g) hJ
      (SlabSpace.blockProj A hA g).measurable hN hreal.poly hni I
    have e : (timeSlab T).indicator (M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T
        (SlabSpace.blockProj A hA g).val) = M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T
        (SlabSpace.blockProj A hA g).val := by
      unfold kGammaRemGSlab
      rw [Set.indicator_indicator, Set.inter_self]
    rw [e]
    exact hm
  have hFV : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      ∀ x ∈ timeSlab T, M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T
        (SlabSpace.blockProj A hA g).val x ∈ V := fun g x hx => by
    rw [kGammaRemGSlab_of_mem I hx]
    exact kGammaRemG_mem I hIV hpolyV (hfA g x) ((hS g).hfT x)
  have hFT : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      ∀ x ∈ timeSlab T, M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T
        (SlabSpace.blockProj A hA g).val x ∈ lowerSubspace 𝒯.deg (γ₀ + α + α + 2) :=
    fun g x hx => by
      rw [kGammaRemGSlab_of_mem I hx]
      exact (hsp g).1 x hx
  have hFB : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      M.SingularBoundOn timeZeroDist (γ₀ + α + α + 2) (min ζ η'' + 2)
        (C₀ * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ) *
          ‖SlabSpace.blockProj A hA g‖) (timeSlab T)
        (M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T (SlabSpace.blockProj A hA g).val) :=
    fun g => (hsp g).2.1.indicator_self
  have hFsup : ∀ g : M.SlabSpace timeZeroDist ⊤ (γ₀ + α + α) η'' (timeSlab T),
      ∀ x ∈ timeSlab T, 0 < timeZeroDist x → ∀ i, 𝒯.deg i < γ₀ + α + α + 2 →
        |M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T (SlabSpace.blockProj A hA g).val x i| ≤
          C₀ * ((max 1 CGam * CPi + Fintype.card ι * CI) * max 1 CΓ) *
            ‖SlabSpace.blockProj A hA g‖ *
            singularWeight timeZeroDist x ^ (min ζ η'' + 2 - 𝒯.deg i) :=
    fun g x hx _ i hi => by
      rw [kGammaRemGSlab_of_mem I hx]
      exact (hsp g).2.2 x hx i hi
  refine ⟨M.phi4IntegrationOperatorNear T A hA (M.kGammaRemGSlab h r Ppoly I (γ₀ + α + α) T) hFadd
    hFsmul hVc hFmeas hFV hFT hFB hΓK hC hCΓ hγK (le_min hηK.le hηγ.le), ?_,
    exists_unique_phi4_timeSlab_fixedPoint_of_blockOperator_near P hV hW hVα hWα hVVW hreg₁ hreg₂
      hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ hΓ₀ hΓ₁ hCΓ hΓK hγK hηK hηγ hC hR₀ hT hTT₀ A hA
      _ hFadd hFsmul hVc hFmeas hFV hFT hFB hFsup v hv⟩
  intro g x hx
  refine (val_slabOfOperator_of_mem_near g hx (timeZeroDist_pos_of_mem_timeSlab hx)).trans ?_
  exact congrArg _ (kGammaRemGSlab_of_mem I hx)

end Model

end RegularityStructures

end
