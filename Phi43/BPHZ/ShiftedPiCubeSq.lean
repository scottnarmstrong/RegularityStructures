/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedMomentDefs
public import Phi43.BPHZ.PositivePiMomentCubeSq
public import Phi43.BPHZ.PositivePiMomentIPsi
public import Phi43.BPHZ.PositivePiMomentIPsiBound
public import Phi43.BPHZ.GammaFullUniform
public import Phi43.BPHZ.GammaFullGap
import Mathlib.Tactic

/-!
# Shifted moments of `Q_t Π_x I(Ψ³)²`

This is the square input of the moment bounds for the shifted BPHZ models. The shifted integrated
cubic is the Wick-cube increment at the Hairer constant, followed by the shift of the first
renormalisation constant. The linear increment is controlled by the recentred linear field and the
full spatial gradient; the resulting bounds are then combined with Minkowski and the square-product
estimate.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private noncomputable def rawPsiIncrement {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (ω : Ω)
    (x y : ParabolicSpace) : ℝ :=
  hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
    (fun w => hairerPsiField N ξ ω w)

private theorem rawPsiIncrement_eq (N : ℕ) {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
    (hξ : IsSmoothOnSpaceTime (ξ ω)) (x y : ParabolicSpace) :
    rawPsiIncrement N ξ ω x y =
      hairerIPsiRecentred N ξ ω x y +
        ∑ i : Fin 3, gammaFullGrad N ξ i (spaceTimeProj x) ω * (y.2 i - x.2 i) := by
  have hψ : IsSmoothOnSpaceTime (hairerPsiField N ξ ω) :=
    isSmoothOnSpaceTime_hairerPsiField N hξ
  have hc : Continuous (hairerPsiField N ξ ω) :=
    IsSmoothOnSpaceTime.continuous hψ
  have hconv (z : ParabolicSpace) :
      hairerConvolution N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) z =
        ∫ w, hairerKernelTorus N (spaceTimeProj z - w) * hairerPsiField N ξ ω w :=
    hairerConvolution_comp_proj_eq N hc z
  have hgrad (i : Fin 3) (z : ParabolicSpace) :
      hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i z =
        gammaFullGrad N ξ i (spaceTimeProj z) ω := by
    rw [hairerSpatialGradient_eq_integral_torusGrad N i hψ, gammaFullGrad]
  have hrel : ∀ i : Fin 3, CanonicalData.relCoord x y i.succ = y.2 i - x.2 i := by
    intro i
    have hc4 : ∀ (z : ParabolicSpace) (j : Fin 3),
        parabolicCoords z j.succ = z.2 j := by
      intro z j
      fin_cases j <;> rfl
    simp only [CanonicalData.relCoord, hc4]
  unfold rawPsiIncrement
  rw [hairerKernelIncrementPairing_eq N (spaceTimeProj x) (spaceTimeProj y) hc]
  unfold hairerIPsiRecentred
  simp_rw [hconv, hgrad, hrel]
  ring

private theorem rawPsiIncrement_eq_conv (N : ℕ) {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
    (hξ : IsSmoothOnSpaceTime (ξ ω)) (x y : ParabolicSpace) :
    rawPsiIncrement N ξ ω x y =
      gammaFullConv N ξ (spaceTimeProj y) ω - gammaFullConv N ξ (spaceTimeProj x) ω := by
  have hc : Continuous (hairerPsiField N ξ ω) :=
    IsSmoothOnSpaceTime.continuous (isSmoothOnSpaceTime_hairerPsiField N hξ)
  unfold rawPsiIncrement gammaFullConv
  rw [hairerKernelIncrementPairing_eq N (spaceTimeProj x) (spaceTimeProj y) hc]

private theorem measurable_rawPsiIncrement (N : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : ParabolicSpace) :
    Measurable (fun ω => rawPsiIncrement N ξ ω x y) := by
  have heq : (fun ω => rawPsiIncrement N ξ ω x y) =
      fun ω => hairerIPsiRecentred N ξ ω x y +
        ∑ i : Fin 3, gammaFullGrad N ξ i (spaceTimeProj x) ω * (y.2 i - x.2 i) := by
    funext ω
    exact rawPsiIncrement_eq N (hξ.1 ω) x y
  rw [heq]
  have hm : ∀ i : Fin 3, Measurable (fun ω => gammaFullGrad N ξ i (spaceTimeProj x) ω) := by
    intro i
    exact measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      ((measurable_hairerKernelTorusGrad N i).comp
        (measurable_const.sub measurable_id))
  have hsum : Measurable (fun ω => ∑ i : Fin 3,
      gammaFullGrad N ξ i (spaceTimeProj x) ω * (y.2 i - x.2 i)) := by
    exact Finset.measurable_sum _ fun i _ => (hm i).mul measurable_const
  exact (measurable_hairerIPsiRecentred N hξ x y).add hsum

private theorem rawPsiIncrement_lintegral_enorm_pow_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (κ : Kappa)
    {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiCube + κbar / 2)) ^ q := by
  obtain ⟨CR, hCR, hR⟩ := gammaPsiTaylor_gap_lintegral_le.{u} N hρ hκb0 hκb hq
  obtain ⟨CG, hCG, hG⟩ := gammaFull_grad_lintegral_le.{u} N hρ hq
  obtain ⟨CF, hCF, hF⟩ := gammaFull_conv_lintegral_le.{u} N hρ hq
  let C : ℝ := CR + 3 * CG + 2 * CF
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have hprob := hW.isProbabilityMeasure
  let d : ℝ := parabolicSemigroup.scaleDist y x
  have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg y x
  have he0 : 0 ≤ homogeneity κ .iPsiCube + κbar / 2 := by
    have hk := κ.2.1
    have hk' := κ.2.2
    simp only [homogeneity]
    linarith
  have he1 : homogeneity κ .iPsiCube + κbar / 2 ≤ 1 := by
    have hk := κ.2.1
    simp only [homogeneity]
    linarith
  have heR : homogeneity κ .iPsiCube + κbar / 2 ≤ homogeneity κ .iPsi + κbar := by
    have hk := κ.2.1
    simp only [homogeneity]
    linarith
  have hdist : parabolicSemigroup.scaleDist x y = parabolicSemigroup.scaleDist y x := by
    calc
      parabolicSemigroup.scaleDist x y = parabolicNorm (y - x) :=
        (parabolicNorm_sub_prod x y).symm
      _ = parabolicNorm (x - y) := parabolicNorm_sub_comm y x
      _ = parabolicSemigroup.scaleDist y x := parabolicNorm_sub_prod y x
  have hmR : Measurable (fun ω => hairerIPsiRecentred N ξ ω x y) :=
    measurable_hairerIPsiRecentred N hξ x y
  have hmG : ∀ i : Fin 3, Measurable (fun ω =>
      (y.2 i - x.2 i) * gammaFullGrad N ξ i (spaceTimeProj x) ω) := by
    intro i
    have hi : Measurable (fun ω => gammaFullGrad N ξ i (spaceTimeProj x) ω) :=
      measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
        ((measurable_hairerKernelTorusGrad N i).comp
          (measurable_const.sub measurable_id))
    exact hi.const_mul _
  have hmGS : Measurable (fun ω => ∑ i : Fin 3,
      (y.2 i - x.2 i) * gammaFullGrad N ξ i (spaceTimeProj x) ω) := by
    exact Finset.measurable_sum _ fun i _ => hmG i
  have hcoord : ∀ i : Fin 3, |y.2 i - x.2 i| ≤ d := by
    intro i
    have hi := abs_snd_le_parabolicNorm (x.1 - y.1) (x.2 - y.2) i
    calc
      |y.2 i - x.2 i| = |x.2 i - y.2 i| := abs_sub_comm _ _
      _ ≤ parabolicNorm (x.1 - y.1, x.2 - y.2) := hi
      _ = d := by rw [parabolicNorm_sub_prod y x]
  have hnear : ∀ hd : d ≤ 1,
      ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * d ^ (homogeneity κ .iPsiCube + κbar / 2)) ^ q := by
    intro hd
    have hRxy := hR hW hε hξ y x
    rw [hdist] at hRxy
    have hRxy' : ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (CR * d ^ (homogeneity κ .iPsi + κbar)) ^ q := by
      have heq : (fun ω => hairerIPsiRecentred N ξ ω x y) =
          fun ω => gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω := by
        funext ω
        exact hairerIPsiRecentred_eq_gammaPsiTaylor N (hξ.1 ω) x y
      calc
        ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y‖ₑ ^ q ∂P =
            ∫⁻ ω, ‖gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1)
              (y.2 - x.2) ω‖ₑ ^ q ∂P := by
                apply lintegral_congr
                intro ω
                exact congrArg (fun z : ℝ => ‖z‖ₑ ^ q)
                  (congrFun heq ω)
        _ ≤ ENNReal.ofReal (CR * d ^ (homogeneity κ .iPsi + κbar)) ^ q := by
          have hePsi : homogeneity κ .iPsi = 3 / 2 - κ.1 := by
            simp only [homogeneity]
          simpa [d, hePsi] using hRxy
    have hGi : ∀ i : Fin 3,
        ∫⁻ ω, ‖(y.2 i - x.2 i) * gammaFullGrad N ξ i (spaceTimeProj x) ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (CG * d) ^ q := by
      intro i
      have hi := hG hW hε hξ i (spaceTimeProj x)
      have hi' := lintegral_enorm_pow_const_mul_le (y.2 i - x.2 i) hi
      refine hi'.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
      have hcoeff : |y.2 i - x.2 i| * CG ≤ d * CG :=
        mul_le_mul_of_nonneg_right (hcoord i) hCG
      simpa [mul_comm] using hcoeff
    have hG01 := lintegral_enorm_pow_add_le hq (hmG 0).aestronglyMeasurable
      (hmG 1).aestronglyMeasurable (hGi 0) (hGi 1) (by positivity) (by positivity)
    have hG012 := lintegral_enorm_pow_add_le hq
      ((hmG 0).add (hmG 1)).aestronglyMeasurable (hmG 2).aestronglyMeasurable
      hG01 (hGi 2) (by positivity) (by positivity)
    have hmGS' : Measurable (fun ω =>
        ((y.2 0 - x.2 0) * gammaFullGrad N ξ 0 (spaceTimeProj x) ω +
          (y.2 1 - x.2 1) * gammaFullGrad N ξ 1 (spaceTimeProj x) ω) +
          (y.2 2 - x.2 2) * gammaFullGrad N ξ 2 (spaceTimeProj x) ω) :=
      ((hmG 0).add (hmG 1)).add (hmG 2)
    have hsum := lintegral_enorm_pow_add_le hq hmR.aestronglyMeasurable
      hmGS'.aestronglyMeasurable hRxy' hG012 (by positivity) (by positivity)
    have hsum' : ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (CR * d ^ (homogeneity κ .iPsi + κbar) +
          3 * (CG * d)) ^ q := by
      calc
        ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y‖ₑ ^ q ∂P =
            ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y +
              (((y.2 0 - x.2 0) * gammaFullGrad N ξ 0 (spaceTimeProj x) ω +
                (y.2 1 - x.2 1) * gammaFullGrad N ξ 1 (spaceTimeProj x) ω) +
                (y.2 2 - x.2 2) * gammaFullGrad N ξ 2 (spaceTimeProj x) ω)‖ₑ ^ q ∂P := by
                  apply lintegral_congr
                  intro ω
                  have he := rawPsiIncrement_eq N (hξ.1 ω) x y
                  have he' : rawPsiIncrement N ξ ω x y =
                      hairerIPsiRecentred N ξ ω x y +
                        (((y.2 0 - x.2 0) * gammaFullGrad N ξ 0 (spaceTimeProj x) ω +
                          (y.2 1 - x.2 1) * gammaFullGrad N ξ 1 (spaceTimeProj x) ω) +
                          (y.2 2 - x.2 2) * gammaFullGrad N ξ 2 (spaceTimeProj x) ω) := by
                    simpa [Fin.sum_univ_three, mul_comm, add_assoc] using he
                  exact congrArg (fun z : ℝ => ‖z‖ₑ ^ q) he'
        _ ≤ ENNReal.ofReal (CR * d ^ (homogeneity κ .iPsi + κbar) +
            (CG * d + CG * d + CG * d)) ^ q := by
              exact hsum
        _ = ENNReal.ofReal (CR * d ^ (homogeneity κ .iPsi + κbar) +
            3 * (CG * d)) ^ q := by ring_nf
    refine hsum'.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
    have hpowR : d ^ (homogeneity κ .iPsi + κbar) ≤
        d ^ (homogeneity κ .iPsiCube + κbar / 2) :=
      Real.rpow_le_rpow_of_exponent_ge' hd0 hd he0 heR
    have hpow1 : d ≤ d ^ (homogeneity κ .iPsiCube + κbar / 2) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' hd0 hd he0 he1
    dsimp [C]
    calc
      CR * d ^ (homogeneity κ .iPsi + κbar) + 3 * (CG * d) ≤
          CR * d ^ (homogeneity κ .iPsiCube + κbar / 2) +
            3 * (CG * d ^ (homogeneity κ .iPsiCube + κbar / 2)) := by
        gcongr
      _ ≤ (CR + 3 * CG + 2 * CF) * d ^ (homogeneity κ .iPsiCube + κbar / 2) := by
        have hdE : 0 ≤ d ^ (homogeneity κ .iPsiCube + κbar / 2) :=
          Real.rpow_nonneg hd0 _
        calc
          CR * d ^ (homogeneity κ .iPsiCube + κbar / 2) +
              3 * (CG * d ^ (homogeneity κ .iPsiCube + κbar / 2)) =
              (CR + 3 * CG) * d ^ (homogeneity κ .iPsiCube + κbar / 2) := by ring
          _ ≤ (CR + 3 * CG + 2 * CF) * d ^
              (homogeneity κ .iPsiCube + κbar / 2) := by
            exact mul_le_mul_of_nonneg_right (by linarith) hdE
  by_cases hd : d ≤ 1
  · exact hnear hd
  · have hd1 : 1 ≤ d := (not_le.mp hd).le
    have hmy : Measurable (fun ω => gammaFullConv N ξ (spaceTimeProj y) ω) :=
      measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
        ((measurable_constantsComparison_hairerKernelTorus N).comp
          (measurable_const.sub measurable_id))
    have hmx : Measurable (fun ω => gammaFullConv N ξ (spaceTimeProj x) ω) :=
      measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
        ((measurable_constantsComparison_hairerKernelTorus N).comp
          (measurable_const.sub measurable_id))
    have hy := hF hW hε hξ (spaceTimeProj y)
    have hx := hF hW hε hξ (spaceTimeProj x)
    have hfar := lintegral_enorm_pow_sub_le hq hmy.aestronglyMeasurable
      hmx.aestronglyMeasurable hy hx hCF hCF
    have heq : (fun ω => rawPsiIncrement N ξ ω x y) =
        fun ω => gammaFullConv N ξ (spaceTimeProj y) ω -
          gammaFullConv N ξ (spaceTimeProj x) ω := by
      funext ω
      exact rawPsiIncrement_eq_conv N (hξ.1 ω) x y
    have hfar' : ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (CF + CF) ^ q := by
      calc
        ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y‖ₑ ^ q ∂P =
            ∫⁻ ω, ‖gammaFullConv N ξ (spaceTimeProj y) ω -
              gammaFullConv N ξ (spaceTimeProj x) ω‖ₑ ^ q ∂P := by
                apply lintegral_congr
                intro ω
                exact congrArg (fun z : ℝ => ‖z‖ₑ ^ q) (congrFun heq ω)
        _ ≤ ENNReal.ofReal (CF + CF) ^ q := hfar
    have hpow : 1 ≤ d ^ (homogeneity κ .iPsiCube + κbar / 2) :=
      Real.one_le_rpow hd1 he0
    refine hfar'.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
    dsimp [C]
    calc
      CF + CF ≤ (CR + 3 * CG + 2 * CF) * 1 := by linarith
      _ ≤ (CR + 3 * CG + 2 * CF) * d ^
          (homogeneity κ .iPsiCube + κbar / 2) :=
        mul_le_mul_of_nonneg_left hpow hC

private theorem rawPsiIncrement_sub_eq (N : ℕ) {Ω : Type*} {ξ ξ' : Ω → SpaceTime → ℝ}
    {ω : Ω} (hξ : IsSmoothOnSpaceTime (ξ ω)) (hξ' : IsSmoothOnSpaceTime (ξ' ω))
    (x y : ParabolicSpace) :
    rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y =
      (hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) +
        ∑ i : Fin 3, (y.2 i - x.2 i) *
          (gammaFullGrad N ξ i (spaceTimeProj x) ω -
            gammaFullGrad N ξ' i (spaceTimeProj x) ω) := by
  rw [rawPsiIncrement_eq N hξ x y, rawPsiIncrement_eq N hξ' x y]
  simp only [Fin.sum_univ_three, mul_sub]
  ring

private theorem rawPsiIncrement_sub_lintegral_enorm_pow_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar) (hθ : 0 < θ)
    (hκθ : κbar + θ ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            parabolicSemigroup.scaleDist y x ^ (homogeneity κ .iPsiCube + κbar / 2)) ^ q := by
  have hθκ : θ < κ.1 - κbar := by
    have hk := κ.2.1
    linarith
  have hθ1 : θ ≤ 1 / 4 := by
    have hk := κ.2.2
    linarith
  obtain ⟨CR, hCR, hR⟩ := gammaPsiTaylor_sub_gap_lintegral_le.{u} N hρ hρ' hκb0 hθ hθκ hq
  obtain ⟨CG, hCG, hG⟩ := gammaFull_grad_sub_lintegral_le.{u} N hρ hρ' hθ hθ1 hq
  obtain ⟨CF, hCF, hF⟩ := gammaFull_conv_sub_lintegral_le.{u} N hρ hρ' hθ hθ1 hq
  let C : ℝ := CR + 3 * CG + 2 * CF
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have hprob := hW.isProbabilityMeasure
  let d : ℝ := parabolicSemigroup.scaleDist y x
  let m : ℝ := (max ε ε') ^ θ
  have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg y x
  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have he0 : 0 ≤ homogeneity κ .iPsiCube + κbar / 2 := by
    have hk := κ.2.1
    have hk' := κ.2.2
    simp only [homogeneity]
    linarith
  have he1 : homogeneity κ .iPsiCube + κbar / 2 ≤ 1 := by
    have hk := κ.2.1
    simp only [homogeneity]
    linarith
  have heR : homogeneity κ .iPsiCube + κbar / 2 ≤ homogeneity κ .iPsi + κbar := by
    have hk := κ.2.1
    simp only [homogeneity]
    linarith
  have hePsi : homogeneity κ .iPsi = 3 / 2 - κ.1 := by
    simp only [homogeneity]
  have hdist : parabolicSemigroup.scaleDist x y = parabolicSemigroup.scaleDist y x := by
    calc
      parabolicSemigroup.scaleDist x y = parabolicNorm (y - x) :=
        (parabolicNorm_sub_prod x y).symm
      _ = parabolicNorm (x - y) := parabolicNorm_sub_comm y x
      _ = parabolicSemigroup.scaleDist y x := parabolicNorm_sub_prod y x
  have hcoord : ∀ i : Fin 3, |y.2 i - x.2 i| ≤ d := by
    intro i
    have hi := abs_snd_le_parabolicNorm (x.1 - y.1) (x.2 - y.2) i
    calc
      |y.2 i - x.2 i| = |x.2 i - y.2 i| := abs_sub_comm _ _
      _ ≤ parabolicNorm (x.1 - y.1, x.2 - y.2) := hi
      _ = d := by rw [parabolicNorm_sub_prod y x]
  have hmR : Measurable (fun ω =>
      hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) :=
    (measurable_hairerIPsiRecentred N hξ x y).sub
      (measurable_hairerIPsiRecentred N hξ' x y)
  have hmG : ∀ i : Fin 3, Measurable (fun ω =>
      (y.2 i - x.2 i) *
        (gammaFullGrad N ξ i (spaceTimeProj x) ω -
          gammaFullGrad N ξ' i (spaceTimeProj x) ω)) := by
    intro i
    have hi : Measurable (fun ω => gammaFullGrad N ξ i (spaceTimeProj x) ω -
        gammaFullGrad N ξ' i (spaceTimeProj x) ω) :=
      (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
        ((measurable_hairerKernelTorusGrad N i).comp
          (measurable_const.sub measurable_id))).sub
        (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ')
          ((measurable_hairerKernelTorusGrad N i).comp
            (measurable_const.sub measurable_id)))
    exact hi.const_mul _
  have hnear : ∀ hd : d ≤ 1,
      ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * m * d ^
          (homogeneity κ .iPsiCube + κbar / 2)) ^ q := by
    intro hd
    have hRxy := hR hW hε hε' hξ hξ' y x
    rw [hdist] at hRxy
    have hRxy' : ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y -
        hairerIPsiRecentred N ξ' ω x y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (CR * m * d ^ (homogeneity κ .iPsi + κbar)) ^ q := by
      have heq : (fun ω => hairerIPsiRecentred N ξ ω x y -
          hairerIPsiRecentred N ξ' ω x y) =
          fun ω => gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
            gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω := by
        funext ω
        rw [hairerIPsiRecentred_eq_gammaPsiTaylor N (hξ.1 ω) x y,
          hairerIPsiRecentred_eq_gammaPsiTaylor N (hξ'.1 ω) x y]
      calc
        ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y‖ₑ ^ q ∂P =
            ∫⁻ ω, ‖gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
              gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω‖ₑ ^ q ∂P := by
                apply lintegral_congr
                intro ω
                exact congrArg (fun z : ℝ => ‖z‖ₑ ^ q) (congrFun heq ω)
        _ ≤ ENNReal.ofReal (CR * m * d ^ (homogeneity κ .iPsi + κbar)) ^ q := by
          simpa [d, m, hePsi, mul_assoc] using hRxy
    have hGi : ∀ i : Fin 3,
        ∫⁻ ω, ‖(y.2 i - x.2 i) *
          (gammaFullGrad N ξ i (spaceTimeProj x) ω -
            gammaFullGrad N ξ' i (spaceTimeProj x) ω)‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (CG * m * d) ^ q := by
      intro i
      have hi := hG hW hε hε' hξ hξ' i (spaceTimeProj x)
      have hi' := lintegral_enorm_pow_const_mul_le (y.2 i - x.2 i) hi
      refine hi'.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
      calc
        |y.2 i - x.2 i| * (CG * m) ≤ d * (CG * m) :=
          mul_le_mul_of_nonneg_right (hcoord i) (mul_nonneg hCG hm0)
        _ = CG * m * d := by ring
    have hG01 := lintegral_enorm_pow_add_le hq (hmG 0).aestronglyMeasurable
      (hmG 1).aestronglyMeasurable (hGi 0) (hGi 1) (by positivity) (by positivity)
    have hG012 := lintegral_enorm_pow_add_le hq
      ((hmG 0).add (hmG 1)).aestronglyMeasurable (hmG 2).aestronglyMeasurable
      hG01 (hGi 2) (by positivity) (by positivity)
    have hmGS : Measurable (fun ω =>
        ((y.2 0 - x.2 0) * (gammaFullGrad N ξ 0 (spaceTimeProj x) ω -
            gammaFullGrad N ξ' 0 (spaceTimeProj x) ω) +
          (y.2 1 - x.2 1) * (gammaFullGrad N ξ 1 (spaceTimeProj x) ω -
            gammaFullGrad N ξ' 1 (spaceTimeProj x) ω)) +
          (y.2 2 - x.2 2) * (gammaFullGrad N ξ 2 (spaceTimeProj x) ω -
            gammaFullGrad N ξ' 2 (spaceTimeProj x) ω)) :=
      ((hmG 0).add (hmG 1)).add (hmG 2)
    have hsum := lintegral_enorm_pow_add_le hq hmR.aestronglyMeasurable
      hmGS.aestronglyMeasurable hRxy' hG012 (by positivity) (by positivity)
    have hsum' : ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y -
        rawPsiIncrement N ξ' ω x y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (CR * m * d ^ (homogeneity κ .iPsi + κbar) +
          3 * (CG * m * d)) ^ q := by
      calc
        ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y‖ₑ ^ q ∂P =
            ∫⁻ ω, ‖(hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) +
              (((y.2 0 - x.2 0) * (gammaFullGrad N ξ 0 (spaceTimeProj x) ω -
                  gammaFullGrad N ξ' 0 (spaceTimeProj x) ω) +
                (y.2 1 - x.2 1) * (gammaFullGrad N ξ 1 (spaceTimeProj x) ω -
                  gammaFullGrad N ξ' 1 (spaceTimeProj x) ω)) +
                (y.2 2 - x.2 2) * (gammaFullGrad N ξ 2 (spaceTimeProj x) ω -
                  gammaFullGrad N ξ' 2 (spaceTimeProj x) ω))‖ₑ ^ q ∂P := by
                    apply lintegral_congr
                    intro ω
                    have he := rawPsiIncrement_sub_eq N (hξ.1 ω) (hξ'.1 ω) x y
                    have he' : rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y =
                        (hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) +
                          (((y.2 0 - x.2 0) * (gammaFullGrad N ξ 0 (spaceTimeProj x) ω -
                              gammaFullGrad N ξ' 0 (spaceTimeProj x) ω) +
                            (y.2 1 - x.2 1) * (gammaFullGrad N ξ 1 (spaceTimeProj x) ω -
                              gammaFullGrad N ξ' 1 (spaceTimeProj x) ω)) +
                            (y.2 2 - x.2 2) * (gammaFullGrad N ξ 2 (spaceTimeProj x) ω -
                              gammaFullGrad N ξ' 2 (spaceTimeProj x) ω)) := by
                      simpa [Fin.sum_univ_three, mul_comm, add_assoc] using he
                    exact congrArg (fun z : ℝ => ‖z‖ₑ ^ q) he'
        _ ≤ ENNReal.ofReal (CR * m * d ^ (homogeneity κ .iPsi + κbar) +
            (CG * m * d + CG * m * d + CG * m * d)) ^ q := hsum
        _ = ENNReal.ofReal (CR * m * d ^ (homogeneity κ .iPsi + κbar) +
            3 * (CG * m * d)) ^ q := by ring_nf
    refine hsum'.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
    have hpowR : d ^ (homogeneity κ .iPsi + κbar) ≤
        d ^ (homogeneity κ .iPsiCube + κbar / 2) :=
      Real.rpow_le_rpow_of_exponent_ge' hd0 hd he0 heR
    have hpow1 : d ≤ d ^ (homogeneity κ .iPsiCube + κbar / 2) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' hd0 hd he0 he1
    dsimp [C]
    calc
      CR * m * d ^ (homogeneity κ .iPsi + κbar) + 3 * (CG * m * d) ≤
          CR * m * d ^ (homogeneity κ .iPsiCube + κbar / 2) +
            3 * (CG * m * d ^ (homogeneity κ .iPsiCube + κbar / 2)) := by
        gcongr
      _ ≤ (CR + 3 * CG + 2 * CF) * m *
          d ^ (homogeneity κ .iPsiCube + κbar / 2) := by
        have hdE : 0 ≤ d ^ (homogeneity κ .iPsiCube + κbar / 2) :=
          Real.rpow_nonneg hd0 _
        have hcoef : 0 ≤ CR + 3 * CG + 2 * CF := by positivity
        calc
          CR * m * d ^ (homogeneity κ .iPsiCube + κbar / 2) +
              3 * (CG * m * d ^ (homogeneity κ .iPsiCube + κbar / 2)) =
              (CR + 3 * CG) * m * d ^
                (homogeneity κ .iPsiCube + κbar / 2) := by ring
          _ ≤ (CR + 3 * CG + 2 * CF) * m * d ^
              (homogeneity κ .iPsiCube + κbar / 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith) hm0) hdE
  by_cases hd : d ≤ 1
  · exact hnear hd
  · have hd1 : 1 ≤ d := (not_le.mp hd).le
    have hmy : Measurable (fun ω =>
        gammaFullConv N ξ (spaceTimeProj y) ω -
          gammaFullConv N ξ' (spaceTimeProj y) ω) :=
      (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
        ((measurable_constantsComparison_hairerKernelTorus N).comp
          (measurable_const.sub measurable_id))).sub
        (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ')
          ((measurable_constantsComparison_hairerKernelTorus N).comp
            (measurable_const.sub measurable_id)))
    have hmx : Measurable (fun ω =>
        gammaFullConv N ξ (spaceTimeProj x) ω -
          gammaFullConv N ξ' (spaceTimeProj x) ω) :=
      (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
        ((measurable_constantsComparison_hairerKernelTorus N).comp
          (measurable_const.sub measurable_id))).sub
        (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ')
          ((measurable_constantsComparison_hairerKernelTorus N).comp
            (measurable_const.sub measurable_id)))
    have hy := hF hW hε hε' hξ hξ' (spaceTimeProj y)
    have hx := hF hW hε hε' hξ hξ' (spaceTimeProj x)
    have hfar := lintegral_enorm_pow_sub_le hq hmy.aestronglyMeasurable
      hmx.aestronglyMeasurable hy hx (by positivity) (by positivity)
    have heqy : (fun ω => rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y) =
        fun ω => (gammaFullConv N ξ (spaceTimeProj y) ω -
          gammaFullConv N ξ' (spaceTimeProj y) ω) -
          (gammaFullConv N ξ (spaceTimeProj x) ω -
            gammaFullConv N ξ' (spaceTimeProj x) ω) := by
      funext ω
      rw [rawPsiIncrement_eq_conv N (hξ.1 ω) x y,
        rawPsiIncrement_eq_conv N (hξ'.1 ω) x y]
      ring
    have hfar' : ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y -
        rawPsiIncrement N ξ' ω x y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (2 * CF * m) ^ q := by
      calc
        ∫⁻ ω, ‖rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y‖ₑ ^ q ∂P =
            ∫⁻ ω, ‖(gammaFullConv N ξ (spaceTimeProj y) ω -
              gammaFullConv N ξ' (spaceTimeProj y) ω) -
              (gammaFullConv N ξ (spaceTimeProj x) ω -
                gammaFullConv N ξ' (spaceTimeProj x) ω)‖ₑ ^ q ∂P := by
                  apply lintegral_congr
                  intro ω
                  exact congrArg (fun z : ℝ => ‖z‖ₑ ^ q) (congrFun heqy ω)
        _ ≤ ENNReal.ofReal (CF * m + CF * m) ^ q :=
          lintegral_enorm_pow_sub_le hq hmy.aestronglyMeasurable
            hmx.aestronglyMeasurable hy hx
            (by positivity) (by positivity)
        _ = ENNReal.ofReal (2 * CF * m) ^ q := by ring_nf
    have hpow : 1 ≤ d ^ (homogeneity κ .iPsiCube + κbar / 2) :=
      Real.one_le_rpow hd1 he0
    refine hfar'.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
    dsimp [C]
    calc
      2 * CF * m ≤ (CR + 3 * CG + 2 * CF) * m := by
        gcongr
        linarith
      _ = (CR + 3 * CG + 2 * CF) * m * 1 := by ring
      _ ≤ (CR + 3 * CG + 2 * CF) * m *
          d ^ (homogeneity κ .iPsiCube + κbar / 2) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (by positivity) hm0)

private theorem shiftedPiCubeSq_integral_eq (N : ℕ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} {c : RenormalisationConstants}
    (κ : Kappa) {ω : Ω} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hω : Statements.HasPhi43NoiseGrowth (ξ ω))
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) (x : ParabolicSpace) :
    (canonicalModelOfLift N κ (shiftConst N ρ ε c) (ξ ω)).regPi x
        (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c.1 * rawPsiIncrement N ξ ω x y) ^ 2 := by
  rw [regPi_canonicalModelOfLift_eq_integral (hξ.1 ω) hω _ ht.1 x,
    extensionPi_iPsiCubeSq_eq (hξ.1 ω) x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [show C₁ (shiftConst N ρ ε c) = hairerWickConstant N ρ ε + c.1 by rfl]
  have hfun : (fun w => hairerTreePsiCube N ξ
      (hairerWickConstant N ρ ε + c.1) ω w) =
      (fun w => hairerTreePsiCube N ξ (hairerWickConstant N ρ ε) ω w -
        3 * c.1 * hairerPsiField N ξ ω w) := by
    funext w
    simp only [hairerTreePsiCube]
    ring
  change parabolicSemigroup.kernel t x y *
      (hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (fun w => hairerTreePsiCube N ξ
          (hairerWickConstant N ρ ε + c.1) ω w)) ^ 2 = _
  have hψ : Continuous (hairerPsiField N ξ ω) :=
    continuous_hairerPsiField N hξ.1 ω
  have hcube : Continuous (hairerTreePsiCube N ξ (hairerWickConstant N ρ ε) ω) := by
    unfold hairerTreePsiCube
    fun_prop
  rw [hfun, hairerKernelIncrementPairing_sub_const_mul N _ _ hcube hψ (3 * c.1),
    hairerKernelIncrementPairing_psiCube_eq_gammaWickCube]
  rfl

private theorem shiftedCubeSq_exponent (κ : Kappa) (κbar : ℝ) :
    (homogeneity κ .iPsiCube + κbar / 2) * 2 =
      homogeneity κ .iPsiCubeSq + κbar := by
  simp only [homogeneity]
  ring

private theorem shiftedRpow_two_mul {d : ℝ} (hd : 0 ≤ d) (e : ℝ) :
    (d ^ e) ^ 2 = d ^ (e * 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
  norm_num

private theorem shiftedCubeValue_lintegral_enorm_pow_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (κ : Kappa)
    {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ c : RenormalisationConstants, ‖c‖ ≤ B →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c.1 * rawPsiIncrement N ξ ω x y‖ₑ ^ (2 * q) ∂P ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiCube + κbar / 2)) ^ (2 * q) := by
  obtain ⟨CV, hCV, hV⟩ := gammaWickCube_lintegral_enorm_pow_le_all.{u} N hρ
    (κ := κ) (κbar := κbar / 2) (by linarith) (by linarith) (q := 2 * q) (by omega)
  obtain ⟨CR, hCR, hR⟩ := rawPsiIncrement_lintegral_enorm_pow_le.{u} N hρ κ
    hκb0 hκb (q := 2 * q) (by omega)
  let C : ℝ := CV + 3 * B * CR
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ c hc hg x y
  have hprob := hW.isProbabilityMeasure
  have hVxy := hV hW hε hξ x y
  have hRxy := hR hW hε hξ x y
  have hscalar := lintegral_enorm_pow_const_mul_le (3 * c.1) hRxy
  have hc1 : |3 * c.1| ≤ 3 * B := by
    calc
      |3 * c.1| = 3 * |c.1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
      _ ≤ 3 * B := mul_le_mul_of_nonneg_left (norm_fst_le c |>.trans hc) (by norm_num)
  have hscalar' : ∫⁻ ω, ‖3 * c.1 * rawPsiIncrement N ξ ω x y‖ₑ ^ (2 * q) ∂P ≤
      ENNReal.ofReal (3 * B * parabolicSemigroup.scaleDist y x ^
        (homogeneity κ .iPsiCube + κbar / 2) * CR) ^ (2 * q) := by
    refine hscalar.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _)
    have hd := parabolicSemigroup.scaleDist_nonneg y x
    have hm : 0 ≤ parabolicSemigroup.scaleDist y x ^
        (homogeneity κ .iPsiCube + κbar / 2) := Real.rpow_nonneg hd _
    calc
      |3 * c.1| * (CR * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2)) ≤
          3 * B * (CR * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiCube + κbar / 2)) := by
              gcongr
      _ = 3 * B * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2) * CR := by ring
  have hmV : Measurable (fun ω => gammaWickCube N ρ ε ξ (spaceTimeProj x)
      (spaceTimeProj y) ω) :=
    measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y))
  have hd := parabolicSemigroup.scaleDist_nonneg y x
  have hm : 0 ≤ parabolicSemigroup.scaleDist y x ^
      (homogeneity κ .iPsiCube + κbar / 2) := Real.rpow_nonneg hd _
  have ha : 0 ≤ CV * parabolicSemigroup.scaleDist y x ^
      (homogeneity κ .iPsiCube + κbar / 2) := mul_nonneg hCV hm
  have hb : 0 ≤ 3 * B * parabolicSemigroup.scaleDist y x ^
      (homogeneity κ .iPsiCube + κbar / 2) * CR := by positivity
  have hsum := lintegral_enorm_pow_sub_le (q := 2 * q) (by omega)
    hmV.aestronglyMeasurable
    ((measurable_rawPsiIncrement N hξ x y).const_mul (3 * c.1)).aestronglyMeasurable
    hVxy hscalar' ha hb
  refine hsum.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _)
  dsimp [C]
  calc
    CV * parabolicSemigroup.scaleDist y x ^
        (homogeneity κ .iPsiCube + κbar / 2) +
      3 * B * parabolicSemigroup.scaleDist y x ^
        (homogeneity κ .iPsiCube + κbar / 2) * CR ≤
      (CV + 3 * B * CR) * parabolicSemigroup.scaleDist y x ^
        (homogeneity κ .iPsiCube + κbar / 2) := by
          have heq : (CV + 3 * B * CR) * parabolicSemigroup.scaleDist y x ^
              (homogeneity κ .iPsiCube + κbar / 2) =
              CV * parabolicSemigroup.scaleDist y x ^
                (homogeneity κ .iPsiCube + κbar / 2) +
                3 * B * parabolicSemigroup.scaleDist y x ^
                  (homogeneity κ .iPsiCube + κbar / 2) * CR := by ring
          rw [heq]

private theorem shiftedCubeValue_sub_lintegral_enorm_pow_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar) (hθ : 0 < θ)
    (hκθ : κbar + θ ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ c c' : RenormalisationConstants, ‖c‖ ≤ B → ‖c'‖ ≤ B →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) → ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
            3 * c.1 * rawPsiIncrement N ξ ω x y) -
          (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω -
            3 * c'.1 * rawPsiIncrement N ξ' ω x y)‖ₑ ^ (2 * q) ∂P ≤
          ENNReal.ofReal (C * ((max ε ε') ^ θ + ‖c - c'‖) *
            parabolicSemigroup.scaleDist y x ^
              (homogeneity κ .iPsiCube + κbar / 2)) ^ (2 * q) := by
  have hθκ : θ ≤ κ.1 := by
    have hk := κ.2.1
    linarith
  have hκb : κbar ≤ κ.1 / 2 := by
    linarith
  have hκb0' : 0 ≤ κbar / 2 := by linarith
  have hκb' : κbar / 2 ≤ κ.1 / 2 := by
    linarith
  have hθ1 : θ ≤ 1 / 4 := by
    have hk := κ.2.2
    linarith
  obtain ⟨CV, hCV, hV⟩ := gammaWickCube_sub_lintegral_enorm_pow_le_all.{u} N hρ hρ'
    (κ := κ) (κbar := κbar / 2) (θ := θ) hκb0' hκb' hθ hθκ
    (q := 2 * q) (by omega)
  obtain ⟨CR, hCR, hR⟩ := rawPsiIncrement_sub_lintegral_enorm_pow_le.{u} N hρ hρ'
    κ hκb0 hθ hκθ (q := 2 * q) (by omega)
  obtain ⟨CR', hCR', hR'⟩ := rawPsiIncrement_lintegral_enorm_pow_le.{u} N hρ' κ
    hκb0 hκb (q := 2 * q) (by omega)
  let C : ℝ := CV + 3 * B * CR + 3 * CR'
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' c c' hc hc' hg hg' x y
  have hprob := hW.isProbabilityMeasure
  let d : ℝ := parabolicSemigroup.scaleDist y x
  let m : ℝ := (max ε ε') ^ θ
  let n : ℝ := ‖c - c'‖
  have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg y x
  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hn0 : 0 ≤ n := norm_nonneg _
  have he0 : 0 ≤ homogeneity κ .iPsiCube + κbar / 2 := by
    have hk := κ.2.1
    have hk' := κ.2.2
    simp only [homogeneity]
    linarith
  have hdE : 0 ≤ d ^ (homogeneity κ .iPsiCube + κbar / 2) :=
    Real.rpow_nonneg hd0 _
  have hVxy := hV hW hε hε' hξ hξ' x y
  have hRxy := hR hW hε hε' hξ hξ' x y
  have hR'xy := hR' hW hε' hξ' x y
  have hc1 : |3 * c.1| ≤ 3 * B := by
    calc
      |3 * c.1| = 3 * |c.1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
      _ ≤ 3 * B := mul_le_mul_of_nonneg_left (norm_fst_le c |>.trans hc) (by norm_num)
  have hc1' : |3 * (c.1 - c'.1)| ≤ 3 * n := by
    have hfst : |c.1 - c'.1| ≤ n := by
      change |c.1 - c'.1| ≤ ‖c - c'‖
      simpa [sub_eq_add_neg, Real.norm_eq_abs] using norm_fst_le (c - c')
    calc
      |3 * (c.1 - c'.1)| = 3 * |c.1 - c'.1| := by
        rw [abs_mul, abs_of_nonneg (by norm_num)]
      _ ≤ 3 * n := mul_le_mul_of_nonneg_left hfst (by norm_num)
  have hscalarR := lintegral_enorm_pow_const_mul_le (3 * c.1) hRxy
  have hscalarR' : ∫⁻ ω, ‖3 * c.1 *
      (rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y)‖ₑ ^ (2 * q) ∂P ≤
      ENNReal.ofReal (3 * B * m * d ^
        (homogeneity κ .iPsiCube + κbar / 2) * CR) ^ (2 * q) := by
    refine hscalarR.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _)
    have hcoef : 0 ≤ CR * m * d ^
        (homogeneity κ .iPsiCube + κbar / 2) := by positivity
    calc
      |3 * c.1| * (CR * m * d ^
          (homogeneity κ .iPsiCube + κbar / 2)) ≤
          3 * B * (CR * m * d ^
            (homogeneity κ .iPsiCube + κbar / 2)) :=
        mul_le_mul_of_nonneg_right hc1 hcoef
      _ = 3 * B * m * d ^
          (homogeneity κ .iPsiCube + κbar / 2) * CR := by ring
  have hscalarD := lintegral_enorm_pow_const_mul_le (3 * (c.1 - c'.1)) hR'xy
  have hscalarD' : ∫⁻ ω, ‖3 * (c.1 - c'.1) *
      rawPsiIncrement N ξ' ω x y‖ₑ ^ (2 * q) ∂P ≤
      ENNReal.ofReal (3 * n * d ^
        (homogeneity κ .iPsiCube + κbar / 2) * CR') ^ (2 * q) := by
    refine hscalarD.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _)
    have hcoef : 0 ≤ CR' * d ^
        (homogeneity κ .iPsiCube + κbar / 2) := by positivity
    calc
      |3 * (c.1 - c'.1)| * (CR' * d ^
          (homogeneity κ .iPsiCube + κbar / 2)) ≤
          3 * n * (CR' * d ^
            (homogeneity κ .iPsiCube + κbar / 2)) :=
        mul_le_mul_of_nonneg_right hc1' hcoef
      _ = 3 * n * d ^
          (homogeneity κ .iPsiCube + κbar / 2) * CR' := by ring
  have hmV : Measurable (fun ω => gammaWickCube N ρ ε ξ
      (spaceTimeProj x) (spaceTimeProj y) ω -
      gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω) :=
    (measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y))).sub
      (measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ')
        (measurable_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y)))
  have hmR : Measurable (fun ω => 3 * c.1 *
      (rawPsiIncrement N ξ ω x y - rawPsiIncrement N ξ' ω x y)) :=
    ((measurable_rawPsiIncrement N hξ x y).sub
      (measurable_rawPsiIncrement N hξ' x y)).const_mul (3 * c.1)
  have hmD : Measurable (fun ω => 3 * (c.1 - c'.1) *
      rawPsiIncrement N ξ' ω x y) :=
    (measurable_rawPsiIncrement N hξ' x y).const_mul (3 * (c.1 - c'.1))
  have hfirst := lintegral_enorm_pow_sub_le (q := 2 * q) (by omega)
    hmV.aestronglyMeasurable hmR.aestronglyMeasurable hVxy hscalarR'
    (by positivity) (by positivity)
  have hlast := lintegral_enorm_pow_sub_le (q := 2 * q) (by omega)
    ((hmV.sub hmR).aestronglyMeasurable) hmD.aestronglyMeasurable hfirst hscalarD'
    (by positivity) (by positivity)
  have hident : (fun ω =>
      (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c.1 * rawPsiIncrement N ξ ω x y) -
        (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c'.1 * rawPsiIncrement N ξ' ω x y)) =
      fun ω => (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c.1 * (rawPsiIncrement N ξ ω x y -
            rawPsiIncrement N ξ' ω x y)) -
        3 * (c.1 - c'.1) * rawPsiIncrement N ξ' ω x y := by
    funext ω
    ring
  rw [show (fun ω => ‖
      (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c.1 * rawPsiIncrement N ξ ω x y) -
        (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c'.1 * rawPsiIncrement N ξ' ω x y)‖ₑ ^ (2 * q)) =
      fun ω => ‖((gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c.1 * (rawPsiIncrement N ξ ω x y -
            rawPsiIncrement N ξ' ω x y)) -
        3 * (c.1 - c'.1) * rawPsiIncrement N ξ' ω x y)‖ₑ ^ (2 * q) by
          funext ω
          rw [congrFun hident ω]]
  refine hlast.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _)
  have hcoef1 : 0 ≤ CV * m * d ^
      (homogeneity κ .iPsiCube + κbar / 2) +
      3 * B * m * d ^ (homogeneity κ .iPsiCube + κbar / 2) * CR := by positivity
  have hcoef2 : 0 ≤ 3 * n * d ^
      (homogeneity κ .iPsiCube + κbar / 2) * CR' := by positivity
  have hsum : CV * m * d ^ (homogeneity κ .iPsiCube + κbar / 2) +
      3 * B * m * d ^ (homogeneity κ .iPsiCube + κbar / 2) * CR +
      3 * n * d ^ (homogeneity κ .iPsiCube + κbar / 2) * CR' ≤
      C * (m + n) * d ^ (homogeneity κ .iPsiCube + κbar / 2) := by
    have hbase : 0 ≤ CV + 3 * B * CR := by positivity
    have h1 : CV + 3 * B * CR ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_right (by positivity)
    have h2 : 3 * CR' ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_left hbase
    calc
      CV * m * d ^ (homogeneity κ .iPsiCube + κbar / 2) +
          3 * B * m * d ^ (homogeneity κ .iPsiCube + κbar / 2) * CR +
          3 * n * d ^ (homogeneity κ .iPsiCube + κbar / 2) * CR' =
        (CV + 3 * B * CR) * (m * d ^
          (homogeneity κ .iPsiCube + κbar / 2)) +
          (3 * CR') * (n * d ^
            (homogeneity κ .iPsiCube + κbar / 2)) := by ring
      _ ≤ C * (m * d ^ (homogeneity κ .iPsiCube + κbar / 2)) +
          C * (n * d ^ (homogeneity κ .iPsiCube + κbar / 2)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right h1 (mul_nonneg hm0 hdE))
          (mul_le_mul_of_nonneg_right h2 (mul_nonneg hn0 hdE))
      _ = C * (m + n) * d ^
          (homogeneity κ .iPsiCube + κbar / 2) := by ring
  exact hsum

private theorem measurable_rawPsiIncrement_uncurry (N : ℕ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : ParabolicSpace) :
    Measurable fun z : Ω × ParabolicSpace => rawPsiIncrement N ξ z.1 x z.2 := by
  have heq : (fun z : Ω × ParabolicSpace => rawPsiIncrement N ξ z.1 x z.2) =
      fun z => hairerIPsiRecentred N ξ z.1 x z.2 +
        ∑ i : Fin 3, gammaFullGrad N ξ i (spaceTimeProj x) z.1 *
          (z.2.2 i - x.2 i) := by
    funext z
    exact rawPsiIncrement_eq N (hξ.1 z.1) x z.2
  rw [heq]
  have hmG : ∀ i : Fin 3, Measurable (fun z : Ω × ParabolicSpace =>
      gammaFullGrad N ξ i (spaceTimeProj x) z.1) := by
    intro i
    exact (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      ((measurable_hairerKernelTorusGrad N i).comp
        (measurable_const.sub measurable_id))).comp measurable_fst
  have hmcoord : ∀ i : Fin 3, Measurable (fun z : Ω × ParabolicSpace =>
      z.2.2 i - x.2 i) := by
    intro i
    exact ((measurable_pi_apply i : Measurable (fun v : Fin 3 → ℝ => v i)).comp
      (measurable_snd.comp measurable_snd)).sub measurable_const
  exact (measurable_hairerIPsiRecentred_uncurry N hξ x).add
    (Finset.measurable_sum _ fun i _ => (hmG i).mul (hmcoord i))

theorem regPi_iPsiCubeSq_shift_lintegral_enorm_pow_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ}
    (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ PiShiftSingleBound.{u} N ρ κ κbar q Symbol.iPsiCubeSq B C := by
  obtain ⟨CA, hCA, hA⟩ := shiftedCubeValue_lintegral_enorm_pow_le.{u} N hρ κ
    hκb0 hκb (q := q) hq hB
  have hs : 0 ≤ homogeneity κ .iPsiCubeSq + κbar := by
    have hk := κ.2.1
    have hk' := κ.2.2
    simp only [homogeneity]
    linarith
  obtain ⟨CS, hCS, hM⟩ := lintegral_enorm_semigroup_apply_pow_le.{u} hq hs
  let C : ℝ := CS * CA ^ 2
  have hC : 0 ≤ C := mul_nonneg hCS (sq_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ξ c hc hW hε hξ hg t ht x
  have hprob := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hae : ∀ᵐ ω ∂P,
      (canonicalModelOfLift N κ (shiftConst N ρ ε c) (ξ ω)).regPi x
          (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x =
        ∫ y, parabolicSemigroup.kernel t x y *
          (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
            3 * c.1 * rawPsiIncrement N ξ ω x y) ^ 2 := by
    filter_upwards [Filter.Eventually.of_forall hg] with ω hgω
    exact shiftedPiCubeSq_integral_eq N κ hξ hgω t ht x
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  have hmA : Measurable fun z : Ω × ParabolicSpace =>
      (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj z.2) z.1 -
        3 * c.1 * rawPsiIncrement N ξ z.1 x z.2) ^ 2 :=
    ((measurable_gammaWickCube_proj N hξ (spaceTimeProj x)).sub
      ((measurable_rawPsiIncrement_uncurry N hξ x).const_mul (3 * c.1))).pow_const 2
  have hkey := hM (C₀ := CA ^ 2) (sq_nonneg _) x (F := fun ω y =>
      (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
        3 * c.1 * rawPsiIncrement N ξ ω x y) ^ 2) hmA
    (fun y => by
      have hd : 0 ≤ parabolicSemigroup.scaleDist y x :=
        parabolicSemigroup.scaleDist_nonneg y x
      have h1 := lintegral_enorm_sq_pow_le (P := P)
        (f := fun ω => gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c.1 * rawPsiIncrement N ξ ω x y) (q := q)
        (D := CA * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2))
        (mul_nonneg hCA (Real.rpow_nonneg hd _))
        (hA hW hε hξ c hc hg x y)
      refine h1.trans (le_of_eq ?_)
      congr 2
      rw [mul_pow, shiftedRpow_two_mul hd, shiftedCubeSq_exponent]) ht.1
  simpa [C, mul_assoc] using hkey

theorem regPi_iPsiCubeSq_shift_sub_lintegral_enorm_pow_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar) (hθ : 0 < θ)
    (hκθ : κbar + θ ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ PiShiftSubBound.{u} N ρ ρ' κ κbar θ q Symbol.iPsiCubeSq B C := by
  obtain ⟨CA, hCA, hA⟩ := shiftedCubeValue_lintegral_enorm_pow_le.{u} N hρ κ
    hκb0 (by linarith) (q := q) hq hB
  obtain ⟨CA', hCA', hA'⟩ := shiftedCubeValue_lintegral_enorm_pow_le.{u} N hρ' κ
    hκb0 (by linarith) (q := q) hq hB
  obtain ⟨CD, hCD, hD⟩ := shiftedCubeValue_sub_lintegral_enorm_pow_le.{u} N hρ hρ' κ
    hκb0 hθ hκθ (q := q) hq hB
  have hs : 0 ≤ homogeneity κ .iPsiCubeSq + κbar := by
    have hk := κ.2.1
    have hk' := κ.2.2
    simp only [homogeneity]
    linarith
  obtain ⟨CS, hCS, hM⟩ := lintegral_enorm_semigroup_apply_pow_le.{u} hq hs
  let DA : ℝ := CA + CA'
  let C : ℝ := CS * (2 * CD * DA)
  have hDA : 0 ≤ DA := by
    dsimp [DA]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' c c' hc hc' hW hε hε' hξ hξ' hg hg' t ht x
  have hprob := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hae : ∀ᵐ ω ∂P,
      (canonicalModelOfLift N κ (shiftConst N ρ ε c) (ξ ω)).regPi x
          (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x -
        (canonicalModelOfLift N κ (shiftConst N ρ' ε' c') (ξ' ω)).regPi x
          (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x =
        ∫ y, parabolicSemigroup.kernel t x y *
          ((gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
              3 * c.1 * rawPsiIncrement N ξ ω x y) ^ 2 -
            (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω -
              3 * c'.1 * rawPsiIncrement N ξ' ω x y) ^ 2) := by
    filter_upwards [Filter.Eventually.of_forall hg, Filter.Eventually.of_forall hg']
      with ω hω hω'
    rw [regPi_sub_canonicalModelOfLift_eq_integral (hξ.1 ω) hω (hξ'.1 ω) hω' _ ht.1 x,
      extensionPi_iPsiCubeSq_eq (hξ.1 ω) x, extensionPi_iPsiCubeSq_eq (hξ'.1 ω) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [show C₁ (shiftConst N ρ ε c) = hairerWickConstant N ρ ε + c.1 by rfl,
      show C₁ (shiftConst N ρ' ε' c') = hairerWickConstant N ρ' ε' + c'.1 by rfl]
    have hψ : Continuous (hairerPsiField N ξ ω) := continuous_hairerPsiField N hξ.1 ω
    have hψ' : Continuous (hairerPsiField N ξ' ω) := continuous_hairerPsiField N hξ'.1 ω
    have hcube : Continuous (hairerTreePsiCube N ξ (hairerWickConstant N ρ ε) ω) := by
      unfold hairerTreePsiCube
      fun_prop
    have hcube' : Continuous (hairerTreePsiCube N ξ'
        (hairerWickConstant N ρ' ε') ω) := by
      unfold hairerTreePsiCube
      fun_prop
    rw [mul_sub]
    change parabolicSemigroup.kernel t x y *
        (hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
          (fun w => hairerTreePsiCube N ξ
            (hairerWickConstant N ρ ε + c.1) ω w)) ^ 2 -
        parabolicSemigroup.kernel t x y *
        (hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
          (fun w => hairerTreePsiCube N ξ'
            (hairerWickConstant N ρ' ε' + c'.1) ω w)) ^ 2 = _
    have hfun : (fun w => hairerTreePsiCube N ξ
        (hairerWickConstant N ρ ε + c.1) ω w) =
        (fun w => hairerTreePsiCube N ξ (hairerWickConstant N ρ ε) ω w -
          3 * c.1 * hairerPsiField N ξ ω w) := by
      funext w
      simp only [hairerTreePsiCube]
      ring
    have hfun' : (fun w => hairerTreePsiCube N ξ'
        (hairerWickConstant N ρ' ε' + c'.1) ω w) =
        (fun w => hairerTreePsiCube N ξ' (hairerWickConstant N ρ' ε') ω w -
          3 * c'.1 * hairerPsiField N ξ' ω w) := by
      funext w
      simp only [hairerTreePsiCube]
      ring
    rw [hfun, hfun',
      hairerKernelIncrementPairing_sub_const_mul N _ _ hcube hψ (3 * c.1),
      hairerKernelIncrementPairing_sub_const_mul N _ _ hcube' hψ' (3 * c'.1),
      hairerKernelIncrementPairing_psiCube_eq_gammaWickCube,
      hairerKernelIncrementPairing_psiCube_eq_gammaWickCube]
    simp only [rawPsiIncrement]
    ring
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  let m : ℝ := (max ε ε') ^ θ
  let n : ℝ := ‖c - c'‖
  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hn0 : 0 ≤ n := norm_nonneg _
  have hAmeas : Measurable fun z : Ω × ParabolicSpace =>
      (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj z.2) z.1 -
        3 * c.1 * rawPsiIncrement N ξ z.1 x z.2) :=
    (measurable_gammaWickCube_proj N hξ (spaceTimeProj x)).sub
      ((measurable_rawPsiIncrement_uncurry N hξ x).const_mul (3 * c.1))
  have hA'meas : Measurable fun z : Ω × ParabolicSpace =>
      (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj z.2) z.1 -
        3 * c'.1 * rawPsiIncrement N ξ' z.1 x z.2) :=
    (measurable_gammaWickCube_proj N hξ' (spaceTimeProj x)).sub
      ((measurable_rawPsiIncrement_uncurry N hξ' x).const_mul (3 * c'.1))
  have hF : Measurable fun z : Ω × ParabolicSpace =>
      (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj z.2) z.1 -
          3 * c.1 * rawPsiIncrement N ξ z.1 x z.2) ^ 2 -
        (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj z.2) z.1 -
          3 * c'.1 * rawPsiIncrement N ξ' z.1 x z.2) ^ 2 :=
    (hAmeas.pow_const 2).sub (hA'meas.pow_const 2)
  have hpt : ∀ y : ParabolicSpace,
      ∫⁻ ω, ‖(gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c.1 * rawPsiIncrement N ξ ω x y) ^ 2 -
        (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω -
          3 * c'.1 * rawPsiIncrement N ξ' ω x y) ^ 2‖ₑ ^ q ∂P ≤
      ENNReal.ofReal ((2 * CD * DA) * (m + n) *
        parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCubeSq + κbar)) ^ q := by
    intro y
    have hdy : 0 ≤ parabolicSemigroup.scaleDist y x :=
      parabolicSemigroup.scaleDist_nonneg y x
    have h1 := hD hW hε hε' hξ hξ' c c' hc hc' hg hg' x y
    have h2 := hA hW hε hξ c hc hg x y
    have h3 := hA' hW hε' hξ' c' hc' hg' x y
    have h2' : ∫⁻ ω, ‖gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
        3 * c.1 * rawPsiIncrement N ξ ω x y‖ₑ ^ (2 * q) ∂P ≤
        ENNReal.ofReal (DA * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2)) ^ (2 * q) := by
      refine h2.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCA')
        (Real.rpow_nonneg hdy _)
    have h3' : ∫⁻ ω, ‖gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω -
        3 * c'.1 * rawPsiIncrement N ξ' ω x y‖ₑ ^ (2 * q) ∂P ≤
        ENNReal.ofReal (DA * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2)) ^ (2 * q) := by
      refine h3.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCA)
        (Real.rpow_nonneg hdy _)
    have hmfy : Measurable (fun ω => gammaWickCube N ρ ε ξ (spaceTimeProj x)
        (spaceTimeProj y) ω - 3 * c.1 * rawPsiIncrement N ξ ω x y) :=
      (measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
        (measurable_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y))).sub
        ((measurable_rawPsiIncrement N hξ x y).const_mul (3 * c.1))
    have hmgy : Measurable (fun ω => gammaWickCube N ρ' ε' ξ' (spaceTimeProj x)
        (spaceTimeProj y) ω - 3 * c'.1 * rawPsiIncrement N ξ' ω x y) :=
      (measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ')
        (measurable_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y))).sub
        ((measurable_rawPsiIncrement N hξ' x y).const_mul (3 * c'.1))
    have hsq := lintegral_enorm_sq_sub_sq_pow_le hmfy hmgy hq
      (by positivity : 0 ≤ CD * (m + n) *
        parabolicSemigroup.scaleDist y x ^ (homogeneity κ .iPsiCube + κbar / 2))
      h1 h2' h3'
    refine hsq.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) _)
    have heq : 2 * (CD * (m + n) * parabolicSemigroup.scaleDist y x ^
        (homogeneity κ .iPsiCube + κbar / 2)) *
        (DA * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2)) =
        2 * CD * DA * (m + n) * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCubeSq + κbar) := by
      calc
        2 * (CD * (m + n) * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiCube + κbar / 2)) *
            (DA * parabolicSemigroup.scaleDist y x ^
              (homogeneity κ .iPsiCube + κbar / 2)) =
            2 * CD * DA * (m + n) *
              ((parabolicSemigroup.scaleDist y x ^
                (homogeneity κ .iPsiCube + κbar / 2)) ^ 2) := by ring
        _ = 2 * CD * DA * (m + n) * parabolicSemigroup.scaleDist y x ^
            ((homogeneity κ .iPsiCube + κbar / 2) * 2) := by
              rw [shiftedRpow_two_mul hdy]
        _ = 2 * CD * DA * (m + n) * parabolicSemigroup.scaleDist y x ^
            (homogeneity κ .iPsiCubeSq + κbar) := by
              rw [shiftedCubeSq_exponent]
    exact le_of_eq heq
  have hkey := hM (C₀ := (2 * CD * DA) * (m + n)) (by positivity) x hF
    (fun y => hpt y) ht.1
  simpa [C, m, n, mul_assoc] using hkey

end RegularityStructures.Phi43

end
