/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.StepAux
public import Phi43.LocalLipschitz.Unit
public import Phi43.LocalLipschitz.DuhamelForcing
public import Phi43.Composition.Diff
public import Phi43.RestartDiff.Package
public import Phi43.TimeSlice.HolderBesovBound
public import Phi43.Potential.HolderContraction
public import RegularityStructures.Abstract.Integration.Growth.Setting

/-!
# Distinct-data positive-clock restart step

Distinct-data generalisation of
`RegularityStructures.Phi43.LocalLipschitz.lipschitz_step_of_restartModels`.
The two classical paths have independent initial data. Both restart fixed points
and their realised operators are constructed below; the initial heat difference
is retained in the estimate. The constants are exactly `stepTime` and `stepK`
and do not depend on either initial datum or on the restart time.
-/

public section

open Set RegularityStructures.PDE
open scoped ENNReal

namespace GlobalPhi43.Flow

open RegularityStructures RegularityStructures.Phi43
  RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Potential RegularityStructures.Phi43.Potential
  RegularityStructures.Phi43.LiftBounds RegularityStructures.Inhomogeneity
  RegularityStructures.Phi43.Composition RegularityStructures.Phi43.Restart

/-- The positive-clock restart estimate for two independent initial data. -/
theorem lipschitz_step_of_restartModels_twoData (κ : Kappa) (η : NegExponent) (hη₁ : -2 / 3 < (η : ℝ))
    (hκη : κ.1 < -1 / 2 - η) (N : ℕ) (hN : 3 ≤ N) {L B T s δ : ℝ} (hL : 1 ≤ L) (hB : 1 ≤ B)
    (hs : 0 < s) (hsT : s ≤ T) (hδ : 0 ≤ δ)
    {noise₁ noise₂ : CanonicalNoise} {Cg₁ Cg₂ : ℝ} {q₁ q₂ : ℕ}
    {hg₁ : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise₁.zeta z‖ ≤ Cg₁ * (1 + parabolicNorm z) ^ q₁}
    {hg₂ : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise₂.zeta z‖ ≤ Cg₂ * (1 + parabolicNorm z) ^ q₂}
    {C C' : RenormalisationConstants} {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup}
    {f g : SpaceTime → ℝ} {ψ ψ' : ℝ → C(Torus3, ℝ)}
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise₁ C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise₂ C' Z')
    (hfz : ∀ z : ParabolicSpace, noise₁.zeta z = f (z.1, torusProj z.2))
    (hgz : ∀ z : ParabolicSpace, noise₂.zeta z = g (z.1, torusProj z.2))
    (hgf : Statements.HasPhi43NoiseGrowth f) (hgg : Statements.HasPhi43NoiseGrowth g)
    (hψ : RegularityStructures.IsMassivePotential f ψ) (hψ' : RegularityStructures.IsMassivePotential g ψ')
    (hsize : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B)
    (hsize' : Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B)
    (hdist : Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ)
    (M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup)
    (hC₁ : EnlargedCompat κ
      ((canonicalRenormalisedModel N κ noise₁ Cg₁ q₁ hg₁ C).translate (restartPoint s)) M₁)
    (hC₂ : EnlargedCompat κ
      ((canonicalRenormalisedModel N κ noise₂ Cg₂ q₂ hg₂ C').translate (restartPoint s)) M₂)
    (hreal₁ : M₁.IsRealisingP (annKernel0C N) (gamma κ + phi43Alpha κ + phi43Alpha κ)
      (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF))
    (hreal₂ : M₂.IsRealisingP (annKernel0C N) (gamma κ + phi43Alpha κ + phi43Alpha κ)
      (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF))
    (hgr₁ : ∃ (C₀ C₀' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₁.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C₀ C₀' ρP ρG p q)
    (hgr₂ : ∃ (C₀ C₀' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₂.GrowthModel (gamma κ + phi43Alpha κ + phi43Alpha κ) C₀ C₀' ρP ρG p q)
    (hJ₁ : M₁.IsJointMeasurable) (hJ₂ : M₂.IsJointMeasurable)
    {u₀ v₀ : C(Torus3, ℝ)} {u v : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution (3 * C₁ C - 9 * C₂ C) f u₀ u)
    (hv : IsClassicalSolution (3 * C₁ C' - 9 * C₂ C') g v₀ v)
    (huL : holderBesovENorm η (u s) ≤ ENNReal.ofReal L)
    (hvL : holderBesovENorm η (v s) ≤ ENNReal.ofReal L) :
    ∀ t ∈ Ioc 0 (stepTime κ η hη₁ hκη N hN L B),
      holderBesovENorm η (u (s + t) - v (s + t)) ≤
        ENNReal.ofReal (stepK κ η hη₁ hκη N hN L B) *
          (holderBesovENorm η (u s - v s) + ENNReal.ofReal δ) := by
  intro t ht
  have hη0 : (η : ℝ) ≤ 0 := η.2.le
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hB'1 : 1 ≤ stepB B := hB.trans (le_stepB B)
  have hL'1 : 1 ≤ stepL N κ L B := hL.trans (le_stepL N κ hB0)
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.le, hsT⟩
  have hT₀1 : stepTime κ η hη₁ hκη N hN L B ≤ 1 := restartTime_le_one κ η _ _ _ _ _ _
  have ht1 : t ≤ 1 := ht.2.trans hT₀1
  have hsize₁' : Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal (stepB B) :=
    hsize.trans (ENNReal.ofReal_le_ofReal (le_stepB B))
  have hsize₂' : Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal (stepB B) :=
    hsize'.trans (ENNReal.ofReal_le_ofReal (le_stepB B))
  -- window bounds and differences of the enlarged models at the size `B`
  obtain ⟨c, hc0, hc⟩ := restart_quantitative (κ := κ) N hN
  obtain ⟨cd, hcd0, hcd⟩ := restart_quantitative_diff (κ := κ) N hN
  have hRC₁ := hc hB0 hZ hsI hsize M₁ hC₁ ⟨hreal₁, hgr₁⟩
  have hRC₂ := hc hB0 hZ' hsI hsize' M₂ hC₂ ⟨hreal₂, hgr₂⟩
  unfold RestartConclusion at hRC₁ hRC₂
  obtain ⟨hPi₁, hGam₁, -⟩ := hRC₁
  obtain ⟨hPi₂, hGam₂, -⟩ := hRC₂
  obtain ⟨hdPi, hdGam, -⟩ := hcd hB0 hδ hZ hZ' hsI hsize hsize' hdist M₁ M₂ hC₁ hC₂
    ⟨hreal₁, hgr₁⟩ ⟨hreal₂, hgr₂⟩
  have e := gamma_add_alpha_add_alpha κ
  rw [e] at hPi₁ hGam₁ hPi₂ hGam₂ hdPi hdGam
  have hgrK₁ : ∃ (C₀ C₀' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₁.GrowthModel κ.1 C₀ C₀' ρP ρG p q := e ▸ hgr₁
  have hgrK₂ : ∃ (C₀ C₀' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M₂.GrowthModel κ.1 C₀ C₀' ρP ρG p q := e ▸ hgr₂
  have H₁ := noiseModelHyp_enlarged hC₁ hfz hgf hgrK₁ hPi₁ hB0 hGam₁
  have H₂ := noiseModelHyp_enlarged hC₂ hgz hgg hgrK₂ hPi₂ hB0 hGam₂
  -- forcings
  have hG₁ : ∀ L, DerivHyp (potZeta noise₁.zeta N s) (forcingGc N κ L * stepBg B) L :=
    fun L => derivHyp_zeta_enlarged N H₁ L
  have hG₂ : ∀ L, DerivHyp (potZeta noise₂.zeta N s) (forcingGc N κ L * stepBg B) L :=
    fun L => derivHyp_zeta_enlarged N H₂ L
  have hdGamN := Model.GammaDiffBoundNearOn.toGammaDiffNearOn segmentClosed_hairerTimeWindow
    hGam₁ hGam₂ hdGam
  have hDW := one_le_stepDW B
  have hdd : 0 ≤ δ * stepDW B := mul_nonneg hδ (zero_le_one.trans hDW)
  have hCdPi : δ ≤ δ * stepDW B := le_mul_of_one_le_right hδ hDW
  have hCdGam : gammaDiffChainConst (Fintype.card SymbolF) B δ 16 ≤ δ * stepDW B := by
    rw [gammaDiffChainConst_eq_mul _ _ hδ]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hδ
  have hGd : ∀ L, DerivHyp (potZeta noise₁.zeta N s - potZeta noise₂.zeta N s)
      (forcingGc N κ L * (δ * stepBd B)) L := fun L => by
    have := derivHyp_zeta_sub_enlarged N H₁ H₂ hreal₁.poly hreal₂.poly hdPi hdGamN
      (chainG_nonneg B) hCdPi hCdGam hdd L
    refine derivHyp_mono this (le_of_eq ?_)
    unfold stepBd chainG
    ring
  -- data
  have hψN₁ : ∀ r ∈ Icc (s - 1 / 4) s, holderBesovENorm η (ψ r) ≤ ENNReal.ofReal B :=
    fun r hr => holderBesovENorm_le_of_phi43Size_le hsize ⟨by linarith only [hs, hr.1], by linarith only [hsT, ht1, hr.2]⟩
  have hψN₂ : ∀ r ∈ Icc (s - 1 / 4) s, holderBesovENorm η (ψ' r) ≤ ENNReal.ofReal B :=
    fun r hr => holderBesovENorm_le_of_phi43Size_le hsize' ⟨by linarith only [hs, hr.1], by linarith only [hsT, ht1, hr.2]⟩
  have hψd : ∀ r ∈ Icc (-1 : ℝ) (T + 1), holderBesovENorm η (ψ r - ψ' r) ≤ ENNReal.ofReal δ :=
    fun r hr => holderBesovENorm_sub_le_of_phi43Dist_le hdist hr
  have hP₁ := holderBesovENorm_psiSlice_le N H₁ hfz hgf hψ C η hη0 hB0 hψN₁
  have hP₂ := holderBesovENorm_psiSlice_le N H₂ hgz hgg hψ' C' η hη0 hB0 hψN₂
  have hPd := holderBesovENorm_psiSlice_sub_le N H₁ H₂ hreal₁.poly hreal₂.poly hdPi hdGamN
    (chainG_nonneg B) hCdPi hCdGam hdd hfz hgz hgf hgg hψ hψ' C C' η hη0 hδ
    (fun r hr => hψd r ⟨by linarith only [hs, hr.1], by linarith only [hsT, ht1, hr.2]⟩)
  set P₁ := psiSlice N κ noise₁ C s with hP₁def
  set P₂ := psiSlice N κ noise₂ C' s with hP₂def
  have hLψ := stepLψ_nonneg N κ hB0
  have hw₁ : holderBesovENorm η (u s - P₁) ≤ ENNReal.ofReal (stepL N κ L B) := by
    refine (holderBesovENorm_sub_le_add η _ _).trans ?_
    rw [stepL, ENNReal.ofReal_add (zero_le_one.trans hL) hLψ]
    exact add_le_add huL hP₁
  have hw₂ : holderBesovENorm η (v s - P₂) ≤ ENNReal.ofReal (stepL N κ L B) := by
    refine (holderBesovENorm_sub_le_add η _ _).trans ?_
    rw [stepL, ENNReal.ofReal_add (zero_le_one.trans hL) hLψ]
    exact add_le_add hvL hP₂
  -- the two restart compositions
  have hBg0 := stepBg_nonneg hB0
  obtain ⟨𝒦₁, U₁, h𝒦₁, hU₁, hfix₁, -⟩ := restart_fixedPoint_exists_explicit κ η hη₁ hκη N hN
    (forcingGc N κ) (forcingGc_nonneg N κ) (stepL N κ L B) (stepB B) hL'1 hB'1 hZ hsI hsize₁'
    M₁ hC₁ hreal₁ hgr₁ hJ₁ (u s - P₁) hw₁ (perSmooth_zeta_restart noise₁ N s) hBg0
    (stepBg_le_stepB B) hG₁
  obtain ⟨𝒦₂, U₂, h𝒦₂, hU₂, hfix₂, -⟩ := restart_fixedPoint_exists_explicit κ η hη₁ hκη N hN
    (forcingGc N κ) (forcingGc_nonneg N κ) (stepL N κ L B) (stepB B) hL'1 hB'1 hZ' hsI hsize₂'
    M₂ hC₂ hreal₂ hgr₂ hJ₂ (v s - P₂) hw₂ (perSmooth_zeta_restart noise₂ N s) hBg0
    (stepBg_le_stepB B) hG₂
  have hBdB : δ * stepBd B ≤ stepB B * δ := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (stepBd_le_stepB B) hδ
  have hD := restart_fixedPoint_diff κ η hη₁ hκη N hN (forcingGc N κ) (forcingGc_nonneg N κ)
    (stepL N κ L B) (stepB B) hL'1 hB'1 hδ hZ hZ' hsI hsize₁' hsize₂' hdist M₁ M₂ hC₁ hC₂ hreal₁
    hreal₂ hgr₁ hgr₂ (u s - P₁) (v s - P₂) hw₁ hw₂ (perSmooth_zeta_restart noise₁ N s)
    (perSmooth_zeta_restart noise₂ N s) hBg0 hBg0 (mul_nonneg hδ (stepBd_nonneg B))
    (stepBg_le_stepB B) (stepBg_le_stepB B) hBdB hG₁ hG₂ hGd 𝒦₁ 𝒦₂ U₁ U₂ h𝒦₁ h𝒦₂ hU₁ hU₂
    hfix₁ hfix₂
  -- the near-pair hypotheses at the size `stepB B` on the slab `(0, stepTime]`
  have hB'0 : 0 ≤ stepB B := zero_le_one.trans hB'1
  have hRC₁' := hc hB'0 hZ hsI hsize₁' M₁ hC₁ ⟨hreal₁, hgr₁⟩
  have hRC₂' := hc hB'0 hZ' hsI hsize₂' M₂ hC₂ ⟨hreal₂, hgr₂⟩
  unfold RestartConclusion at hRC₁' hRC₂'
  obtain ⟨hPi₁', hGam₁', hsl₁⟩ := hRC₁'
  obtain ⟨hPi₂', hGam₂', hsl₂⟩ := hRC₂'
  obtain ⟨g₁₀, g₁₁, g₁K⟩ := hsl₁ hT₀1
  obtain ⟨g₂₀, g₂₁, g₂K⟩ := hsl₂ hT₀1
  have hT₀0 : 0 < stepTime κ η hη₁ hκη N hN L B := ht.1.trans_le ht.2
  have hyp₁ : Phi43NearHyp κ N M₁ (stepB B) (gammaChainConst (Fintype.card SymbolF) (stepB B) 16)
      (gammaChainConst (Fintype.card SymbolF) (restartGammaConst c (stepB B)) 16) (stepB B)
      (restartGammaConst c (stepB B)) (stepTime κ η hη₁ hκη N hN L B) :=
    ⟨hPi₁', hGam₁', le_rfl, hgr₁, hB'0, hJ₁, hreal₁, g₁₀, g₁₁, g₁K, le_rfl,
      Composition.gammaChainConst_nonneg' _ _ _, hT₀0, hT₀1⟩
  have hyp₂ : Phi43NearHyp κ N M₂ (stepB B) (gammaChainConst (Fintype.card SymbolF) (stepB B) 16)
      (gammaChainConst (Fintype.card SymbolF) (restartGammaConst c (stepB B)) 16) (stepB B)
      (restartGammaConst c (stepB B)) (stepTime κ η hη₁ hκη N hN L B) :=
    ⟨hPi₂', hGam₂', le_rfl, hgr₂, hB'0, hJ₂, hreal₂, g₂₀, g₂₁, g₂K, le_rfl,
      Composition.gammaChainConst_nonneg' _ _ _, hT₀0, hT₀1⟩
  have hf := isSmoothOnSpaceTime_of_noise hfz
  have hg := isSmoothOnSpaceTime_of_noise hgz
  have hws₁ : ∀ x : Fin 3 → ℝ, (u s - P₁) (torusProj x) =
      u s (torusProj x) - phi43PsiAt N κ noise₁ C (s, x) := fun x => by
    rw [ContinuousMap.sub_apply, hP₁def, psiSlice_apply]
  have hws₂ : ∀ x : Fin 3 → ℝ, (v s - P₂) (torusProj x) =
      v s (torusProj x) - phi43PsiAt N κ noise₂ C' (s, x) := fun x => by
    rw [ContinuousMap.sub_apply, hP₂def, psiSlice_apply]
  have hmild₁ := classical_eq_heat_add_duhamel_sub_cube hyp₁ hN hη₁ hκη noise₁ Cg₁ q₁ hg₁ C hs hC₁
    hf hfz hu (u s - P₁) hws₁ hBg0 (forcingGc_nonneg N κ) hG₁ U₁ 𝒦₁ h𝒦₁ (hfix₁ hT₀1) t ht
  have hmild₂ := classical_eq_heat_add_duhamel_sub_cube hyp₂ hN hη₁ hκη noise₂ Cg₂ q₂ hg₂ C' hs hC₂
    hg hgz hv (v s - P₂) hws₂ hBg0 (forcingGc_nonneg N κ) hG₂ U₂ 𝒦₂ h𝒦₂ (hfix₂ hT₀1) t ht
  -- the three pieces
  set D₁ := duhamel (fun r => nemytskii (cubicHeatNonlinearity (3 * C₁ C - 9 * C₂ C)
    (isSmoothOnSpaceTime_shiftForcing hf s)) r 0) t with hD₁
  set D₂ := duhamel (fun r => nemytskii (cubicHeatNonlinearity (3 * C₁ C' - 9 * C₂ C')
    (isSmoothOnSpaceTime_shiftForcing hg s)) r 0) t with hD₂
  set G₁ : C(Torus3, ℝ) := heatOp t (u s) + D₁ - u (s + t) with hG₁def
  set G₂ : C(Torus3, ℝ) := heatOp t (v s) + D₂ - v (s + t) with hG₂def
  have hsplit : u (s + t) - v (s + t) = (heatOp t (u s - v s) + (D₁ - D₂)) - (G₁ - G₂) := by
    rw [heatOp_sub, hG₁def, hG₂def]; abel
  have hheat : holderBesovENorm η (heatOp t (u s - v s)) ≤ holderBesovENorm η (u s - v s) :=
    holderBesovENorm_heatOp_le η ht.1 _
  have hDd : holderBesovENorm η (D₁ - D₂) ≤ 4 * ENNReal.ofReal δ :=
    holderBesovENorm_duhamel_forcing_sub_le_of_le hf hg (potForcing_of_growth hfz hgf)
      (potForcing_of_growth hgz hgg) hψ hψ' _ _ s ⟨ht.1.le, ht1⟩ η
      (fun r hr => hψd r ⟨by linarith only [hs, hr.1], by linarith only [hsT, ht1, hr.2]⟩)
  -- the cubic term
  set W : ℝ := (holderBesovENorm η ((u s - P₁) - (v s - P₂))).toReal with hW
  set K' : ℝ := compK' κ η hη₁ hκη N hN (forcingGc N κ) (stepL N κ L B) (stepB B) with hK'
  have hK'0 : 0 ≤ K' :=
    (diffConst_nonneg κ η (forcingGc_nonneg N κ) (C₀d := fpCd κ η hη₁ hκη N hN)
      (c := rqC κ N hN) (cd := rqCd κ N hN)
      (Classical.choose_spec
        (phi43FixedPointF_window_nearOne_diff κ hη₁ hκη hN (kernelPair_ann N))).1
      (zero_le_one.trans hL'1 : (0 : ℝ) ≤ stepL N κ L B) (zero_le_one.trans hB'1 : (0 : ℝ) ≤ stepB B)).trans
      (le_max_left _ _)
  have hGd : holderBesovENorm η (G₁ - G₂) ≤ ENNReal.ofReal (K' * (W + δ)) := by
    refine TimeSlice.holderBesovENorm_le_ofReal_of_abs_le hη0 _
      (mul_nonneg hK'0 (add_nonneg ENNReal.toReal_nonneg hδ)) fun y => ?_
    have hy := PDE.torusProj_torusRep y
    rw [← hy]
    have h1 := hmild₁ (torusRep y)
    have h2 := hmild₂ (torusRep y)
    have hG₁y : G₁ (torusProj (torusRep y)) = (𝒦₁ (Model.SlabSpace.cube (phi43ProductF κ)
        (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ)) U₁)).val (t, torusRep y)
          (.old .one) := by
      rw [hG₁def]; simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply]; rw [h1]
      exact sub_sub_cancel _ _
    have hG₂y : G₂ (torusProj (torusRep y)) = (𝒦₂ (Model.SlabSpace.cube (phi43ProductF κ)
        (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ)) U₂)).val (t, torusRep y)
          (.old .one) := by
      rw [hG₂def]; simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply]; rw [h2]
      exact sub_sub_cancel _ _
    rw [ContinuousMap.sub_apply, hG₁y, hG₂y]
    exact hD.2 (t, torusRep y) ht
  -- the final estimate
  set X : ℝ := (holderBesovENorm η (u s - v s)).toReal with hX
  have hXfin : holderBesovENorm η (u s - v s) = ENNReal.ofReal X := by
    rw [hX, ENNReal.ofReal_toReal (holderBesovENorm_lt_top hη0 _).ne]
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  set DY : ℝ := stepDW B * (max 1 (chainG B) * max B 1 * l8Const N κ) with hDY
  have hDY0 : 0 ≤ DY := mul_nonneg (zero_le_one.trans hDW)
    (mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (zero_le_one.trans (le_max_right _ _))) (l8Const_nonneg N κ))
  have hPd' : holderBesovENorm η (P₁ - P₂) ≤ ENNReal.ofReal (δ * DY + 2 * δ) := by
    refine hPd.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hDY]; unfold chainG; ring
  have hWle : W ≤ X + (δ * DY + 2 * δ) := by
    have hY0 : 0 ≤ δ * DY + 2 * δ :=
      add_nonneg (mul_nonneg hδ hDY0) (mul_nonneg (by norm_num) hδ)
    have h1 : holderBesovENorm η ((u s - P₁) - (v s - P₂)) ≤
        ENNReal.ofReal X + ENNReal.ofReal (δ * DY + 2 * δ) := by
      have e2 : (u s - P₁) - (v s - P₂) = (u s - v s) - (P₁ - P₂) := by abel
      rw [e2, ← hXfin]
      exact (holderBesovENorm_sub_le_add η _ _).trans (add_le_add le_rfl hPd')
    rw [← ENNReal.ofReal_add hX0 hY0] at h1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (add_nonneg hX0 hY0)] at this
  have hfin : holderBesovENorm η (u (s + t) - v (s + t)) ≤
      ENNReal.ofReal (X + 4 * δ + K' * (X + δ * DY + 2 * δ + δ)) := by
    rw [hsplit]
    refine (holderBesovENorm_sub_le_add η _ _).trans ?_
    refine (add_le_add (holderBesovENorm_add_le η _ _) hGd).trans ?_
    refine (add_le_add (add_le_add (hheat.trans_eq hXfin) hDd) le_rfl).trans ?_
    have h4 : (4 : ℝ≥0∞) * ENNReal.ofReal δ = ENNReal.ofReal (4 * δ) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    rw [h4, ← ENNReal.ofReal_add hX0 (by positivity),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg hK'0 (add_nonneg ENNReal.toReal_nonneg hδ))]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [add_assoc] using add_le_add (le_refl (X + 4 * δ))
      (mul_le_mul_of_nonneg_left (add_le_add hWle (le_refl δ)) hK'0)
  refine hfin.trans ?_
  rw [hXfin, ← ENNReal.ofReal_add hX0 hδ, ← ENNReal.ofReal_mul (by
    unfold stepK
    exact mul_nonneg (add_nonneg zero_le_one hK'0) (add_nonneg (by norm_num) hDY0))]
  refine ENNReal.ofReal_le_ofReal ?_
  have := step_arith hX0 hδ hK'0 hDY0
  unfold stepK
  rw [← hK', ← hDY]
  exact this

end GlobalPhi43.Flow

end
