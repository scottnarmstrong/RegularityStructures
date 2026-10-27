/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.MW20.LocalPositiveInputs

/-! Collect the landed localized estimates into uniform real allowances
for the owned augmented receiving application. No localization is reproved. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff ENNReal

theorem exists_local_positive_uniform_allowances
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 14) :
    ∃ C > 0, ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ), ∀
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (_hv : ContDiff ℝ ∞ v) (_hJ : ContDiff ℝ ∞ J) (_hY : ContDiff ℝ ∞ Y)
    (_hZ : ContDiff ℝ ∞ Z) (_hV : ContDiff ℝ ∞ V)
    (r d₀ c : ℝ) (_hr : 0 ≤ r) (_hr1 : r < 1 / 2)
    (_hc : 0 ≤ c) (_hc1 : c ≤ 1)
    (_hMpos : 0 < sourceSup v r) (_hscale : d₀ * sourceSup v r ≤ 1)
    (_hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (_hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (_hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (_hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (_hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (_hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (_hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (_hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε))),
    ∃ P₁ P₃ : ℝ, 0 ≤ P₁ ∧ 0 ≤ P₃ ∧
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ (L : ℝ), 0 < L → L ≤ d / 8 → ∀ (T : ℝ) (hT : 0 < T), T ≤ L →
        ∀ y ∈ pastBall x L,
        d ^ (3 / 2 - 5 * ε) * T ^ 2 * |sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x y| ≤
          P₁ * ∑ a ∈ sourceSchauderExponents ε, T ^ a * L ^ ((3 / 2 - 5 * ε) - a)) ∧
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ y ∈ sourceCylinder r, y ∈ symmetricBall x (d / 2) →
        ∀ z ∈ sourceCylinder r, z ∈ symmetricBall y (d / 4) →
        d ^ (3 / 2 - 5 * ε) * |expansion v Y Z x z - expansion v Y Z x y - expansion v Y Z y z| ≤
          P₃ * ∑ a ∈ sourceSchauderExponents ε,
            pdist x y ^ a * pdist y z ^ ((3 / 2 - 5 * ε) - a)) ∧
      (radiusSourceUSup (sourceExpansion v Y Z) r d₀).toReal + P₁ + P₃ ≤
        C * (sourceSup v r + c *
          ((weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ (3 / 2 - 5 * ε)).toReal + sourceSup v r)) := by
  let γ := (3 / 2 : ℝ) - 5 * ε
  let K₃ := 936 * ((4 : ℝ) ^ γ + 1)
  have hK₃ : 0 ≤ K₃ := by dsimp [K₃]; positivity
  have hC₁ := localPositiveP2Constant_pos hsmall
  refine ⟨6 + localPositiveP2Constant ε + K₃, by positivity, ?_⟩
  intro Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV r d₀ c hr hr1 hc hc1 hMpos hscale
    hbudgetY hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD
  let M := sourceSup v r
  let S := (weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal
  let P₁ := localPositiveP2Allowance ε M S c
  let P₃ := sourceFullThreePointAllowance v Y Z ε r d₀ c
  have hS : 0 ≤ S := ENNReal.toReal_nonneg
  refine ⟨P₁, P₃, localPositiveP2Allowance_nonneg hsmall hMpos.le hS hc, ?_, ?_, ?_, ?_⟩
  · dsimp [P₃, sourceFullThreePointAllowance]
    positivity
  · intro d hd x hx L hL hLd T hT hTL y hy
    have hf := source_formal_forcing_weighted_positive Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV
      hr hr1 hd.1 hd.2 hT hTL hLd hε hsmall hc hc1
      hbudgetY hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD hMpos hscale hx
    have he := localScalarSup_bound (sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x)
      (pastBall x L) ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hf.1).ge hy
    have hw := mul_le_mul_of_nonneg_left he
      (mul_nonneg (Real.rpow_nonneg hd.1.le ((3 / 2 : ℝ) - 5 * ε)) (sq_nonneg T))
    apply hw.trans
    simpa only [P₁, localPositiveP2Allowance, M, S, γ, mul_assoc] using hf.2
  · intro d hd x hx y hyD hy z hzD hz
    exact source_three_point_weighted_radius_input_positive v Y Z hv hY hZ hr hr1 hd.1 hd.2
      hε hsmall hc hc1 hbudgetY hbudgetZ hMpos
      ((mul_le_mul_of_nonneg_right hd.2 hMpos.le).trans hscale) hx hyD hy hzD hz
  · let A := M + c * (S + M)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hMA : M ≤ A := by dsimp [A]; nlinarith only [mul_nonneg hc (add_nonneg hS hMpos.le)]
    have hca : c * (S + M) ≤ A := by dsimp [A]; linarith only [hMpos]
    have hB := source_radiusSourceUSup_parent_bound_positive
      (sourceCubicRegularity_of_contDiff (hv.of_le (by simp))) hr
      (by linarith : 0 ≤ (1 / 2 : ℝ) - 3 * ε) (by linarith : 0 ≤ (1 : ℝ) - 2 * ε)
      hc hc1 hMpos hscale hbudgetY hbudgetZ
    have hBr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hB
    rw [ENNReal.toReal_ofReal (by positivity)] at hBr
    have hP₁ : P₁ ≤ localPositiveP2Constant ε * A :=
      localPositiveP2Allowance_price hsmall hMpos.le hS hc
    have hP₃ : P₃ ≤ K₃ * A := by
      have hh := mul_le_mul_of_nonneg_left hca hK₃
      dsimp only [P₃, sourceFullThreePointAllowance, K₃, A, M, S, γ] at hh ⊢
      convert hh using 1
      ring
    have hh := add_le_add (add_le_add (hBr.trans
      (mul_le_mul_of_nonneg_left hMA (by norm_num : (0 : ℝ) ≤ 6))) hP₁) hP₃
    convert hh using 1
    ring

end GlobalPhi43.Local
