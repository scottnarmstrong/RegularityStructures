/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Composition.Exists
public import Phi43.Composition.DiffConsts
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# The two-model restart composition

The uniform Lipschitz bound of the solution map [Hai14, Thm. 7.8, Cor. 7.12, Prop. 9.8].
`restart_fixedPoint_diff`: on the slab `(0, compTime L' B]` of the one-model restart composition
(`restart_fixedPoint_exists_explicit`), for two lifts of sizes `≤ B` (`phi43Size`) and distance
`≤ δ` (`phi43Dist`), two enlarged models as in the two-model restart package
(`restart_quantitative_diff`), two data `w₁, w₂` with `‖wᵢ‖_η ≤ L'` and two forcings with constants
`Bgᵢ ≤ B` and difference constant `Bd ≤ B δ`, any two solutions `Uᵢ = -𝒦ᵢ (Uᵢ⋆³) + vᵢ` of radius
`≤ compR₀ L' B + 1` satisfy `‖U₁; U₂‖ ≤ K' (‖w₁ - w₂‖_η + δ)` and the same bound for the difference
of the `1`-coefficients of `𝒦ᵢ (Uᵢ⋆³)`, with the explicit constant `K' = compK' L' B`.
-/

public section

open Set
open scoped ENNReal

namespace RegularityStructures.Phi43.Composition

open RegularityStructures.Inhomogeneity RegularityStructures.Phi43.Restart
  RegularityStructures.Phi43.LiftBounds

private theorem aux_fp {δv A1 A2 τ t R G δH dC lC B Wd δ Dc Bd : ℝ} (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) (ht : 0 ≤ t) (hR : 0 ≤ R) (hG : 0 ≤ G) (hτ : τ ≤ 1)
    (hdC : 0 ≤ dC) (hlC : 0 ≤ lC) (hB : 0 ≤ B) (hWd : 0 ≤ Wd) (hδ : 0 ≤ δ) (hDc : 0 ≤ Dc)
    (hδH : δH = Dc * δ) (hBd : Bd ≤ B * δ) (hδv : δv = 0 + dC * Wd + lC * Bd) :
    2 * (δv + A1 * τ * (4 * t * R * G * δH) + τ * δH * (t * R * G) * A2) ≤
      2 * (dC + lC * B + (A1 * (4 * (t * R * G)) + t * R * G * A2) * Dc) * (Wd + δ) := by
  subst hδH hδv
  have hF : 0 ≤ t * R * G := mul_nonneg (mul_nonneg ht hR) hG
  have hP : 0 ≤ (A1 * (4 * (t * R * G)) + t * R * G * A2) * Dc * δ := by positivity
  have h1 : A1 * τ * (4 * t * R * G * (Dc * δ)) ≤ A1 * (4 * (t * R * G)) * Dc * δ := by
    have e : A1 * τ * (4 * t * R * G * (Dc * δ)) = τ * (A1 * (4 * (t * R * G)) * Dc * δ) := by
      ring
    rw [e]
    exact mul_le_of_le_one_left (by positivity) hτ
  have h2 : τ * (Dc * δ) * (t * R * G) * A2 ≤ t * R * G * A2 * Dc * δ := by
    have e : τ * (Dc * δ) * (t * R * G) * A2 = τ * (t * R * G * A2 * Dc * δ) := by ring
    rw [e]
    exact mul_le_of_le_one_left (by positivity) hτ
  have h3 : lC * Bd ≤ lC * B * δ := by
    have := mul_le_mul_of_nonneg_left hBd hlC
    linarith [this]
  have h4 : 0 ≤ dC * δ := mul_nonneg hdC hδ
  have h5 : 0 ≤ lC * B * Wd := mul_nonneg (mul_nonneg hlC hB) hWd
  have h6 : 0 ≤ (A1 * (4 * (t * R * G)) + t * R * G * A2) * Dc * Wd := by positivity
  nlinarith [h1, h2, h3, h4, h5, h6, hP]

private theorem aux_slice {S d X δ Dc w δH : ℝ} (hS : 0 ≤ S) (hd : 0 ≤ d) (hX : 0 ≤ X)
    (hDc : 0 ≤ Dc) (hδ : δ ≤ X) (hδ0 : 0 ≤ δ) (hw : w ≤ 1) (hδH : δH = Dc * δ) :
    S * (d * X + δH) * w ≤ S * (d + Dc) * X := by
  subst hδH
  have h1 : S * (d * X + Dc * δ) * w ≤ S * (d * X + Dc * δ) :=
    mul_le_of_le_one_right (by positivity) hw
  have h2 : S * (d * X + Dc * δ) ≤ S * (d * X + Dc * X) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hS
  linarith [h1, h2, show S * (d * X + Dc * X) = S * (d + Dc) * X by ring]

/-- **The two-model restart composition.** -/
theorem restart_fixedPoint_diff (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ))
    (hκη : κ.1 < -1 / 2 - η) (N : ℕ) (hN : 3 ≤ N) (Gc : ℕ → ℝ) (hGc : ∀ L, 0 ≤ Gc L) :
    ∀ L' B : ℝ, 1 ≤ L' → 1 ≤ B → ∀ {δ : ℝ}, 0 ≤ δ → ∀ {T s : ℝ} {ψ ψ' : ℝ → C(Torus3, ℝ)}
      {noise noise' : CanonicalNoise} {Cg Cg' : ℝ} {q q' : ℕ}
      {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
      {hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
        ‖iteratedFDeriv ℝ k noise'.zeta z‖ ≤ Cg' * (1 + parabolicNorm z) ^ q'}
      {C C' : RenormalisationConstants}
      {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup},
      Statements.IsRenormalisedCanonicalModel N κ noise C Z →
      Statements.IsRenormalisedCanonicalModel N κ noise' C' Z' → s ∈ Icc (0 : ℝ) T →
      Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
      Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
      Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
      ∀ (M₁' M₂' : Model (phi43RegularityStructureF κ) parabolicSemigroup),
      EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate (restartPoint s))
        M₁' →
      EnlargedCompat κ
        ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate (restartPoint s)) M₂' →
      ∀ (hreal₁ : M₁'.IsRealisingP (annKernel0C N) (gamma κ + phi43Alpha κ + phi43Alpha κ)
          (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF))
        (hreal₂ : M₂'.IsRealisingP (annKernel0C N) (gamma κ + phi43Alpha κ + phi43Alpha κ)
          (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF)),
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₁'.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q) →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
        M₂'.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C' C'' ρP ρG p q) →
      ∀ (w₁ w₂ : C(Torus3, ℝ)), holderBesovENorm η w₁ ≤ ENNReal.ofReal L' →
        holderBesovENorm η w₂ ≤ ENNReal.ofReal L' →
      ∀ {g₁ g₂ : ParabolicSpace → ℝ} (hgs₁ : PerSmooth g₁) (hgs₂ : PerSmooth g₂)
        {Bg₁ Bg₂ Bd : ℝ} (hBg₁ : 0 ≤ Bg₁) (hBg₂ : 0 ≤ Bg₂), 0 ≤ Bd → Bg₁ ≤ B → Bg₂ ≤ B →
        Bd ≤ B * δ →
      ∀ (hG₁ : ∀ L, DerivHyp g₁ (Gc L * Bg₁) L) (hG₂ : ∀ L, DerivHyp g₂ (Gc L * Bg₂) L),
        (∀ L, DerivHyp (g₁ - g₂) (Gc L * Bd) L) →
      ∀ (𝒦₁ : M₁'.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)) →ₗ[ℝ]
            M₁'.SlabSpace timeZeroDist phi43SectorV (gamma κ) η
              (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)))
        (𝒦₂ : M₂'.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η)
            (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)) →ₗ[ℝ]
            M₂'.SlabSpace timeZeroDist phi43SectorV (gamma κ) η
              (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)))
        (U₁ : M₁'.SlabSpace timeZeroDist phi43SectorV (gamma κ) η
          (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)))
        (U₂ : M₂'.SlabSpace timeZeroDist phi43SectorV (gamma κ) η
          (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B))),
      (∀ g, ∀ x ∈ timeSlab (compTime κ η hη₁ hκη N hN Gc L' B), (𝒦₁ g).val x =
        lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
          (M₁'.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ)
            phi43IntegrationF (gamma κ + phi43Alpha κ + phi43Alpha κ)
            (Model.SlabSpace.blockProj phi43XiFreeF
              (Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M₁')
              g).val x)) →
      (∀ g, ∀ x ∈ timeSlab (compTime κ η hη₁ hκη N hN Gc L' B), (𝒦₂ g).val x =
        lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
          (M₂'.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ)
            phi43IntegrationF (gamma κ + phi43Alpha κ + phi43Alpha κ)
            (Model.SlabSpace.blockProj phi43XiFreeF
              (Model.gammaMap_blockProj_of_isBlockInvariant (phi43XiFreeF_isBlockInvariant κ) M₂')
              g).val x)) →
      ‖U₁‖ ≤ compR₀ η Gc L' B + 1 → ‖U₂‖ ≤ compR₀ η Gc L' B + 1 →
      (∀ ht : compTime κ η hη₁ hκη N hN Gc L' B ≤ 1,
        U₁ = -𝒦₁ (Model.SlabSpace.cube (phi43ProductF κ)
          (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) U₁) +
          phi43InhomTheta κ η M₁' hreal₁.poly ht (toHolderBesov η w₁) hgs₁ hBg₁ hGc hG₁) →
      (∀ ht : compTime κ η hη₁ hκη N hN Gc L' B ≤ 1,
        U₂ = -𝒦₂ (Model.SlabSpace.cube (phi43ProductF κ)
          (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * η) U₂) +
          phi43InhomTheta κ η M₂' hreal₂.poly ht (toHolderBesov η w₂) hgs₂ hBg₂ hGc hG₂) →
      M₁'.SingularDiffBoundOn M₂' timeZeroDist (gamma κ) η
        (compK' κ η hη₁ hκη N hN Gc L' B * ((holderBesovENorm η (w₁ - w₂)).toReal + δ))
        (timeSlab (compTime κ η hη₁ hκη N hN Gc L' B)) U₁.val U₂.val ∧
      ∀ x ∈ timeSlab (compTime κ η hη₁ hκη N hN Gc L' B),
        |(𝒦₁ (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
            (3 * η) U₁)).val x (SymbolF.old .one) -
          (𝒦₂ (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
            (3 * η) U₂)).val x (SymbolF.old .one)| ≤
          compK' κ η hη₁ hκη N hN Gc L' B * ((holderBesovENorm η (w₁ - w₂)).toReal + δ) := by
  have hC₀ := (Classical.choose_spec
    (phi43FixedPointF_window_nearOne κ hη₁ hκη hN (kernelPair_ann N))).1
  obtain ⟨hC₀d, hfpd⟩ := Classical.choose_spec
    (phi43FixedPointF_window_nearOne_diff κ hη₁ hκη hN (kernelPair_ann N))
  obtain ⟨hCsd, htsd⟩ := Classical.choose_spec
    (TimeSlice.phi43_one_coeff_fixedPoint_diff_le κ hη₁ hκη hN (kernelPair_ann N))
  obtain ⟨hc0, hc⟩ := Classical.choose_spec (restart_quantitative (κ := κ) N hN)
  obtain ⟨hcd0, hcd⟩ := Classical.choose_spec (restart_quantitative_diff (κ := κ) N hN)
  intro L' B hL hB δ hδ T s ψ ψ' noise noise' Cg Cg' q q' hg hg' C C' Z Z' hZ hZ' hs hsize
    hsize' hdist M₁' M₂' hC₁ hC₂ hreal₁ hreal₂ hgr₁ hgr₂ w₁ w₂ hw₁ hw₂ g₁ g₂ hgs₁ hgs₂ Bg₁ Bg₂ Bd
    hBg₁ hBg₂ hBd hBgB₁ hBgB₂ hBdB hG₁ hG₂ hGd 𝒦₁ 𝒦₂ U₁ U₂ h𝒦₁ h𝒦₂ hU₁ hU₂ hfix₁ hfix₂
  have hB0 : 0 ≤ B := by linarith
  have hL0 : 0 ≤ L' := by linarith
  have hRC₁ := hc hB0 hZ hs hsize M₁' hC₁ ⟨hreal₁, hgr₁⟩
  have hRC₂ := hc hB0 hZ' hs hsize' M₂' hC₂ ⟨hreal₂, hgr₂⟩
  unfold RestartConclusion at hRC₁ hRC₂
  obtain ⟨hPi₁, hGam₁, hslab₁⟩ := hRC₁
  obtain ⟨hPi₂, hGam₂, hslab₂⟩ := hRC₂
  obtain ⟨hdPi, hdGam, hdslab⟩ := hcd hB0 hδ hZ hZ' hs hsize hsize' hdist M₁' M₂' hC₁ hC₂
    ⟨hreal₁, hgr₁⟩ ⟨hreal₂, hgr₂⟩
  have hT₀1 : compTime κ η hη₁ hκη N hN Gc L' B ≤ 1 := restartTime_le_one κ η Gc _ _ _ L' B
  have hT₀0 : 0 < compTime κ η hη₁ hκη N hN Gc L' B :=
    restartTime_pos κ η hGc hC₀ hC₀d hL0 hB0
  obtain ⟨hΓ₁₀, hΓ₁₁, hΓ₁K⟩ := hslab₁ hT₀1
  obtain ⟨hΓ₂₀, hΓ₂₁, hΓ₂K⟩ := hslab₂ hT₀1
  obtain ⟨hdΓ₀, hdΓ₁, hdΓK⟩ := hdslab hT₀1
  obtain ⟨δ₁, hδ₁⟩ : ∃ x : ℝ, x = diffW (rqCd κ N hN) B * δ := ⟨_, rfl⟩
  obtain ⟨δH, hδH⟩ : ∃ x : ℝ, x = diffChain (rqC κ N hN) (rqCd κ N hN) B * δ := ⟨_, rfl⟩
  have hδδ₁ : δ ≤ δ₁ := hδ₁ ▸ le_mul_of_one_le_left hδ (one_le_diffW _ B)
  have hδδH : δ ≤ δH := hδH ▸ le_mul_of_one_le_left hδ (one_le_diffChain _ _ B)
  have hδH0 : 0 ≤ δH := hδ.trans hδδH
  have hdPiH : M₁'.PiDiffBoundOn M₂' (gamma κ + phi43Alpha κ + phi43Alpha κ) δH
      hairerTimeWindow := fun i hi t ht x hx =>
    (hdPi i hi t ht x hx).trans (mul_le_mul_of_nonneg_right hδδH (Real.rpow_nonneg ht.1.le _))
  have hrs : restartGammaDiffConst (rqCd κ N hN) B * δ ≤ δ₁ :=
    hδ₁ ▸ mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
  have hch₁ : gammaDiffChainConst (Fintype.card SymbolF) B δ₁ 16 ≤ δH := by
    rw [hδ₁, hδH]; exact gammaDiffChainConst_diffW_le hδ (Or.inl rfl)
  have hch₂ : gammaDiffChainConst (Fintype.card SymbolF) (restartGammaConst (rqC κ N hN) B) δ₁ 16
      ≤ δH := by
    rw [hδ₁, hδH]; exact gammaDiffChainConst_diffW_le hδ (Or.inr rfl)
  have hdv := singularDiffBoundOn_phi43InhomTheta κ η M₁' M₂' hreal₁.poly hreal₂.poly hT₀1
    (toHolderBesov η w₁) (toHolderBesov η w₂) hgs₁ hgs₂ hBg₁ hBg₂ hBd hGc hG₁ hG₂ hGd
  have hWd : ‖toHolderBesov η w₁ - toHolderBesov η w₂‖ =
      (holderBesovENorm η (w₁ - w₂)).toReal := by
    rw [← toHolderBesov_sub, norm_toHolderBesov]
  have hWd0 : 0 ≤ (holderBesovENorm η (w₁ - w₂)).toReal := ENNReal.toReal_nonneg
  have hdC := datumConst_nonneg η 3
  have hlC : 0 ≤ Datum.liftConst 3 (thetaKc Gc) := Datum.liftConst_nonneg (thetaKc_nonneg hGc)
  have hδv0 : 0 ≤ 0 + datumConst η 3 * ‖toHolderBesov η w₁ - toHolderBesov η w₂‖ +
      Datum.liftConst 3 (thetaKc Gc) * Bd := by positivity
  have hR0 : 0 ≤ datumR η Gc L' B := datumR_nonneg η hGc hL0 hB0
  have hSD := hfpd M₁' M₂' (CPi := B) (CGam := chainG B) (CΓ := chainΓ (rqC κ N hN) B)
    (CGam₁ := B) (CΓ₁ := restartGammaConst (rqC κ N hN) B) (δ₁ := δ₁) (R₀ := datumR η Gc L' B)
    (δ := δH) _ _ hPi₁ hPi₂ hGam₁ hGam₂ le_rfl hgr₁ hgr₂ hB0 hreal₁ hreal₂ hΓ₁₀ hΓ₁₁ hΓ₁K hΓ₂₀
    hΓ₂₁ hΓ₂K le_rfl (chainΓ_nonneg _ B) hdPiH (hdGam.mono_const hδδ₁) hch₁
    (hdΓ₀.mono_const hrs) (hdΓ₁.mono_const hrs) (hdΓK.mono_const hrs) hch₂ hδH0 hδv0 hR0 hT₀0
    hT₀1 (restartTime_le_fixedPointTime_diff κ η Gc _ _ _ L' B) 𝒦₁ 𝒦₂ h𝒦₁ h𝒦₂ hdv U₁ U₂ hU₁ hU₂
    (hfix₁ hT₀1) (hfix₂ hT₀1)
  have hX0 : 0 ≤ (holderBesovENorm η (w₁ - w₂)).toReal + δ := add_nonneg hWd0 hδ
  have hτ0 : 0 ≤ compTime κ η hη₁ hκη N hN Gc L' B ^ theta κ η := Real.rpow_nonneg hT₀0.le _
  have hτ1 : compTime κ η hη₁ hκη N hN Gc L' B ^ theta κ η ≤ 1 :=
    Real.rpow_le_one hT₀0.le hT₀1 (theta_pos κ hη₁ hκη).le
  have hd0 := diffConst_nonneg κ η hGc (C₀d := fpCd κ η hη₁ hκη N hN) (c := rqC κ N hN)
    (cd := rqCd κ N hN) hC₀d hL0 hB0
  have hA1 := fpConstDiff_nonneg κ (c := rqC κ N hN) (B := B) hC₀d
  have hA2 := fpConstDiff'_nonneg κ hC₀d (rqC κ N hN) B
  have hDc : 0 ≤ diffChain (rqC κ N hN) (rqCd κ N hN) B :=
    zero_le_one.trans (one_le_diffChain _ _ B)
  have hbig := aux_fp (δv := 0 + datumConst η 3 * ‖toHolderBesov η w₁ - toHolderBesov η w₂‖ +
      Datum.liftConst 3 (thetaKc Gc) * Bd) hA1 hA2 (sq_nonneg (phi43ProductF κ).truncMulConst)
    (pow_nonneg (by linarith : (0 : ℝ) ≤ datumR η Gc L' B + 1) 3)
    (pow_nonneg (by linarith [chainΓ_nonneg (rqC κ N hN) B] :
      (0 : ℝ) ≤ 1 + chainΓ (rqC κ N hN) B) 4) hτ1 hdC hlC hB0 (norm_nonneg _) hδ hDc hδH
    hBdB rfl
  have hSD1 := hSD.mono hbig
  rw [hWd] at hSD1
  refine ⟨hSD1.mono (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0), fun x hx => ?_⟩
  have hU0 := mul_nonneg hd0 hX0
  have h1 := htsd M₁' M₂' (CPi := B) (CGam := chainG B) (CΓ := chainΓ (rqC κ N hN) B)
    (CGam₁ := B) (CΓ₁ := restartGammaConst (rqC κ N hN) B) (δ₁ := δ₁) (R₀ := datumR η Gc L' B)
    (δ := δH) hPi₁ hPi₂ hGam₁ hGam₂ le_rfl hgr₁ hgr₂ hB0 hreal₁ hreal₂ hΓ₁₀ hΓ₁₁ hΓ₁K hΓ₂₀
    hΓ₂₁ hΓ₂K le_rfl (chainΓ_nonneg _ B) hdPiH (hdGam.mono_const hδδ₁) hch₁
    (hdΓ₀.mono_const hrs) (hdΓ₁.mono_const hrs) (hdΓK.mono_const hrs) hch₂ hδH0 hU0 hR0 hT₀1
    𝒦₁ 𝒦₂ h𝒦₁ h𝒦₂ U₁ U₂ hU₁ hU₂ hSD1 x hx
  have hS0 := sliceDiffConst_nonneg κ hCsd (rqC κ N hN) B hR0
  have hw0 : 0 ≤ x.1 ^ ((3 * (η : ℝ) + 2) / 2) := Real.rpow_nonneg hx.1.le _
  have h2 := aux_slice hS0 hd0 hX0 hDc (le_add_of_nonneg_left hWd0) hδ
    (rpow_time_le_one hη₁ hT₀1 hx) hδH
  refine h1.trans (h2.trans ?_)
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) hX0

end RegularityStructures.Phi43.Composition

end
