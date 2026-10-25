/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Composition.Structural
public import Phi43.FixedPointF.WindowNear
public import Phi43.FixedPointFDiff.WindowNearDiff
public import Phi43.TimeSlice.OneCoeff
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# The one-model restart composition

The local solution of [Hai14, Thm. 7.8 and Prop. 9.8 (local part)], with the constants tracked.
`restart_fixedPoint_exists`: at a restart time `s ∈ [0, T]` of a lift `Z` of size `≤ B`
(`phi43Size`), for every enlarged model `M'` compatible with the restarted canonical model of the
noise, realising, with qualitative growth and jointly measurable, every continuous datum `w` with
`‖w‖_η ≤ L'` and every smooth periodic forcing `g` with derivative bounds `Gc L · Bg`, `Bg ≤ B`, the
window fixed point `U = -𝒦 (U⋆³) + v` with inhomogeneity `v = phi43InhomTheta (w, g)` exists on the
slab `(0, t₀ L' B]`, with `‖U‖ ≤ R₀ L' B + 1`, and the `1`-coefficient of `𝒦 (U⋆³)` is bounded by
`K L' B` on the slab. The functions `t₀`, `R₀`, `K` are the explicit `restartTime`, `datumR`,
`sliceConst` of `Composition.Consts` at structural constants depending only on `(κ, N, η)` (and on
the forcing constants `Gc`).
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.Composition

open RegularityStructures.Inhomogeneity RegularityStructures.Phi43.Restart
  RegularityStructures.Phi43.LiftBounds

/-- The datum embedded in `𝒞^η` has norm at most `L'`. -/
theorem norm_toHolderBesov_le_of_enorm (η : NegExponent) {w : C(Torus3, ℝ)} {L' : ℝ}
    (hL : 0 ≤ L') (hw : holderBesovENorm η w ≤ ENNReal.ofReal L') : ‖toHolderBesov η w‖ ≤ L' := by
  rw [norm_toHolderBesov]
  exact ENNReal.toReal_le_of_le_ofReal hL hw

/-- **The one-model restart composition**, with the explicit constants `compTime`,
`compR₀`, `compK`. -/
theorem restart_fixedPoint_exists_explicit (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ))
    (hκη : κ.1 < -1 / 2 - η) (N : ℕ) (hN : 3 ≤ N) (Gc : ℕ → ℝ) (hGc : ∀ L, 0 ≤ Gc L) :
      ∀ L' B : ℝ, 1 ≤ L' → 1 ≤ B → ∀ {T s : ℝ} {ψ : ℝ → C(Torus3, ℝ)} {noise : CanonicalNoise}
        {Cg : ℝ} {q : ℕ}
        {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
          ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
        {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup},
        Statements.IsRenormalisedCanonicalModel N κ noise C Z → s ∈ Icc (0 : ℝ) T →
        Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup),
        EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s))
          M' →
        ∀ (hreal : M'.IsRealisingP (annKernel0C N) (gamma κ + phi43Alpha κ + phi43Alpha κ)
          (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF)),
        (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
          M'.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q) →
        M'.IsJointMeasurable →
        ∀ (w : C(Torus3, ℝ)), holderBesovENorm η w ≤ ENNReal.ofReal L' →
        ∀ {g : ParabolicSpace → ℝ} (hgs : PerSmooth g) {Bg : ℝ} (hBg : 0 ≤ Bg), Bg ≤ B →
        ∀ (hG : ∀ L, DerivHyp g (Gc L * Bg) L),
        ∃ (𝒦 : M'.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)) →ₗ[ℝ]
            M'.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)))
          (U : M'.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B))),
          (∀ g : M'.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
              (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)), ∀ x ∈ timeSlab (compTime κ η hη₁ hκη N hN Gc L' B), (𝒦 g).val x =
            lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
              (M'.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ)
                phi43IntegrationF (gamma κ + phi43Alpha κ + phi43Alpha κ)
                (Model.SlabSpace.blockProj phi43XiFreeF
                  (Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M')
                  g).val x)) ∧
          ‖U‖ ≤ compR₀ η Gc L' B + 1 ∧
          (∀ ht : compTime κ η hη₁ hκη N hN Gc L' B ≤ 1,
            U = -𝒦 (Model.SlabSpace.cube (phi43ProductF κ)
              (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) U) +
              phi43InhomTheta κ η M' hreal.poly ht (toHolderBesov η w) hgs hBg hGc hG) ∧
          ∀ x ∈ timeSlab (compTime κ η hη₁ hκη N hN Gc L' B),
            |(𝒦 (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
              (3 * η) U)).val x (SymbolF.old .one)| ≤ compK κ η hη₁ hκη N hN Gc L' B := by
  obtain ⟨hC₀, hfp⟩ := Classical.choose_spec
    (phi43FixedPointF_window_nearOne κ hη₁ hκη hN (kernelPair_ann N))
  have hC₀d := (Classical.choose_spec
    (phi43FixedPointF_window_nearOne_diff κ hη₁ hκη hN (kernelPair_ann N))).1
  obtain ⟨hCs, hts⟩ := Classical.choose_spec
    (TimeSlice.phi43_one_coeff_fixedPoint_le κ hη₁ hκη hN (kernelPair_ann N))
  obtain ⟨hc0, hc⟩ := Classical.choose_spec (restart_quantitative (κ := κ) N hN)
  intro L' B hL hB T s ψ noise Cg q hg C Z hZ hs hsize M' hC hreal hgr hJ w hw g hgs Bg hBg hBgB hG
  have hB0 : 0 ≤ B := by linarith
  have hRC := hc hB0 hZ hs hsize M' hC ⟨hreal, hgr⟩
  unfold RestartConclusion at hRC
  obtain ⟨hPi, hGam, hslab⟩ := hRC
  set T₀ := compTime κ η hη₁ hκη N hN Gc L' B with hT₀
  have hT₀1 : T₀ ≤ 1 := restartTime_le_one κ η Gc _ _ _ L' B
  have hT₀0 : 0 < T₀ := restartTime_pos κ η hGc hC₀ hC₀d (by linarith) hB0
  obtain ⟨hΓ0, hΓ1, hΓK⟩ := hslab hT₀1
  have hR0 : 0 ≤ datumR η Gc L' B := datumR_nonneg η hGc (by linarith) hB0
  set v := phi43InhomTheta κ η M' hreal.poly hT₀1 (toHolderBesov η w) hgs hBg hGc hG with hvdef
  have hv : ‖v‖ ≤ datumR η Gc L' B := by
    refine (norm_phi43InhomTheta_le κ η M' hreal.poly hT₀1 (toHolderBesov η w) hgs hBg hGc
      hG).trans ?_
    unfold datumR
    have h1 := datumConst_nonneg η 3
    have h2 : 0 ≤ Datum.liftConst 3 (thetaKc Gc) := Datum.liftConst_nonneg (thetaKc_nonneg hGc)
    have hwL := norm_toHolderBesov_le_of_enorm η (by linarith) hw
    have := mul_le_mul_of_nonneg_left hwL h1
    have := mul_le_mul_of_nonneg_left hBgB h2
    linarith
  obtain ⟨𝒦, h𝒦, U, ⟨hU, hfix⟩, -⟩ := hfp M' (CGam := chainG B) (CΓ := chainΓ (rqC κ N hN) B) v hPi hGam
    le_rfl hgr hB0 hJ hreal hΓ0 hΓ1 hΓK le_rfl (chainΓ_nonneg _ B) hR0 hT₀0 hT₀1
    (restartTime_le_fixedPointTime κ η Gc _ _ _ L' B) hv
  refine ⟨𝒦, U, h𝒦, hU, fun _ => hfix, fun x hx => ?_⟩
  have h1 := hts M' (CGam := chainG B) (CΓ := chainΓ (rqC κ N hN) B) hPi hGam le_rfl hgr hB0 hreal hΓ0 hΓ1
    hΓK le_rfl (chainΓ_nonneg _ B) hT₀1 𝒦 h𝒦 U hU x hx
  refine h1.trans ?_
  have hK0 := sliceConst_nonneg κ (c := rqC κ N hN) hCs hB0 hR0
  have hw1 := rpow_time_le_one hη₁ hT₀1 hx
  have := mul_le_mul_of_nonneg_left hw1 hK0
  unfold compK
  unfold sliceConst at this hK0 ⊢
  rw [tsC]
  linarith

/-- **The one-model restart composition**, existential form. -/
theorem restart_fixedPoint_exists (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ))
    (hκη : κ.1 < -1 / 2 - η) (N : ℕ) (hN : 3 ≤ N) (Gc : ℕ → ℝ) (hGc : ∀ L, 0 ≤ Gc L) :
    ∃ t₀ R₀ K : ℝ → ℝ → ℝ,
      (∀ L' B : ℝ, 1 ≤ L' → 1 ≤ B → 0 < t₀ L' B ∧ t₀ L' B ≤ 1 ∧ 0 ≤ R₀ L' B ∧ 0 ≤ K L' B) ∧
      ∀ L' B : ℝ, 1 ≤ L' → 1 ≤ B → ∀ {T s : ℝ} {ψ : ℝ → C(Torus3, ℝ)} {noise : CanonicalNoise}
        {Cg : ℝ} {q : ℕ}
        {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
          ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
        {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup},
        Statements.IsRenormalisedCanonicalModel N κ noise C Z → s ∈ Icc (0 : ℝ) T →
        Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup),
        EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s))
          M' →
        ∀ (hreal : M'.IsRealisingP (annKernel0C N) (gamma κ + phi43Alpha κ + phi43Alpha κ)
          (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF)),
        (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
          M'.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q) →
        M'.IsJointMeasurable →
        ∀ (w : C(Torus3, ℝ)), holderBesovENorm η w ≤ ENNReal.ofReal L' →
        ∀ {g : ParabolicSpace → ℝ} (hgs : PerSmooth g) {Bg : ℝ} (hBg : 0 ≤ Bg), Bg ≤ B →
        ∀ (hG : ∀ L, DerivHyp g (Gc L * Bg) L),
        ∃ (𝒦 : M'.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab (t₀ L' B)) →ₗ[ℝ]
            M'.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab (t₀ L' B)))
          (U : M'.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab (t₀ L' B))),
          (∀ g : M'.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
              (timeSlab (t₀ L' B)), ∀ x ∈ timeSlab (t₀ L' B), (𝒦 g).val x =
            lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
              (M'.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ)
                phi43IntegrationF (gamma κ + phi43Alpha κ + phi43Alpha κ)
                (Model.SlabSpace.blockProj phi43XiFreeF
                  (Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M')
                  g).val x)) ∧
          ‖U‖ ≤ R₀ L' B + 1 ∧
          (∀ ht : t₀ L' B ≤ 1,
            U = -𝒦 (Model.SlabSpace.cube (phi43ProductF κ)
              (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) U) +
              phi43InhomTheta κ η M' hreal.poly ht (toHolderBesov η w) hgs hBg hGc hG) ∧
          ∀ x ∈ timeSlab (t₀ L' B),
            |(𝒦 (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
              (3 * η) U)).val x (SymbolF.old .one)| ≤ K L' B := by
  refine ⟨compTime κ η hη₁ hκη N hN Gc, compR₀ η Gc, compK κ η hη₁ hκη N hN Gc,
    fun L' B hL hB => ⟨?_, restartTime_le_one κ η Gc _ _ _ L' B,
      datumR_nonneg η hGc (by linarith) (by linarith), ?_⟩,
    restart_fixedPoint_exists_explicit κ η hη₁ hκη N hN Gc hGc⟩
  · exact restartTime_pos κ η hGc
      (Classical.choose_spec (phi43FixedPointF_window_nearOne κ hη₁ hκη hN (kernelPair_ann N))).1
      (Classical.choose_spec
        (phi43FixedPointF_window_nearOne_diff κ hη₁ hκη hN (kernelPair_ann N))).1
      (by linarith) (by linarith)
  · exact sliceConst_nonneg κ (Classical.choose_spec
      (TimeSlice.phi43_one_coeff_fixedPoint_le κ hη₁ hκη hN (kernelPair_ann N))).1 (by linarith)
      (datumR_nonneg η hGc (by linarith) (by linarith))

end RegularityStructures.Phi43.Composition

end
