module

public import GlobalPhi43.MW20.KernelSecondReconstruction
public import GlobalPhi43.MW20.KernelCoordinateBoundary
public import GlobalPhi43.MW20.KernelNormClosure
public import GlobalPhi43.MW20.SecondProductAssembly

/-! Full signed second-product assembly with actual source tests and
the chosen optimal coefficient. No reconstruction error is a caller input. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Signed bound for Lemma 2.10. The D counterterm retains J, while
the reconstruction and coordinate tests retain the distinct V field. -/
theorem kernel_secondProduct_product_bound (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    (x : ParabolicSpace) {T ε : ℝ} (hT : 0 < T) (hT₁ : T < 1)
    (hε : 0 < ε) (hsmall : ε < 1 / 14)
    {Hv HU Hν NA NV NX : ℝ} (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν)
    (hNA : 0 ≤ NA) (hNV : 0 ≤ NV) (hNX : 0 ≤ NX)
    (hvnorm : scalarHolderSeminorm v (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hUnorm : localAffineSeminorm (sourceExpansion v Y Z) (pastBall x T) (3 / 2 - 5 * ε) ≤ ENNReal.ofReal HU)
    (hνnorm : localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) (pastBall x T)
      (1 / 2 - 5 * ε) ≤ ENNReal.ofReal Hν)
    (hAnorm : recenteredASeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε Y V C₂ ≤ ENNReal.ofReal NA)
    (hVnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) (-1 - 2 * ε) V ≤ ENNReal.ofReal NV)
    (hXnorm : recenteredXVSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε V ≤ ENNReal.ofReal NX)
    {M N ND : ℝ} (hND : 0 ≤ ND)
    (hsup : ∀ a ∈ pastBall x T, |v a| ≤ M)
    (hsupν : ∀ a ∈ pastBall x T, ‖sourceAffineCoefficient v Y Z a‖ ≤ N)
    (hDnorm : recenteredDSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε Z V J C₂ ≤ ENNReal.ofReal ND) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT)
      (fun y => (v y - v x) * V y + 3 * C₂ * (v y + J y)) x| ≤
      (3 * Hv * NA + HU * NV + 3 * Hν * NX) * T ^ (1 / 2 - 7 * ε) /
        (1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)) +
      ND * T ^ (-(1 / 2) - 5 * ε) + 3 * M * (NA * T ^ (-4 * ε)) + 3 * N * (NX * T ^ (-2 * ε)) := by
  have hrec := kernel_secondProduct_reconstruction Φ hΦ v Y Z V C₂ hv hY hZ hV x hT hT₁ hε hsmall
    hHv hHU hHν hNA hNV hNX hvnorm hUnorm hνnorm hAnorm hVnorm hXnorm
  have hx : x ∈ closure (pastBall x T) := reconstruction_mem_closure_pastBall x x hT
    (by simpa only [pdist, sub_self, abs_zero, Real.sqrt_zero, norm_zero, max_self] using hT.le) le_rfl
  have hvx := source_sup_bound_closure v hv.continuous (pastBall x T) hsup hx
  have hνc := (sourceAffineCoefficient_contDiff v Y Z hv hY hZ).continuous
  have hνx : ‖sourceAffineCoefficient v Y Z x‖ ≤ N := by
    simpa only [abs_norm] using source_sup_bound_closure _ hνc.norm (pastBall x T)
      (fun a ha => by simpa only [abs_norm] using hsupν a ha) hx
  have hAc : Continuous (fun p : ParabolicSpace × ParabolicSpace => (Y p.2 - Y p.1) * V p.2 - C₂) := by fun_prop
  have hDc : Continuous (fun p : ParabolicSpace × ParabolicSpace => (Z p.2 - Z p.1) * V p.2 - 3 * C₂ * J p.2) := by fun_prop
  have ha := mw20_localTestSeminorm_closure_test_bound Φ hΦ (pastBall x T) (Ioo 0 1) (-4 * ε)
    _ hAc hNA hAnorm hx hT hT₁.le ⟨hT, hT₁⟩
  have hd := mw20_localTestSeminorm_closure_test_bound Φ hΦ (pastBall x T) (Ioo 0 1) (-(1 / 2) - 5 * ε)
    _ hDc hND hDnorm hx hT hT₁.le ⟨hT, hT₁⟩
  rw [← reconstruction_pastSmooth_eq_density Φ hΦ hT hT₁.le] at ha hd
  have hxtest := coordinate_test_bound_of_mem_closure Φ hΦ (pastBall x T) ε V hV.continuous hNX hXnorm hx hT hT₁
  let μ := (infiniteKernelMeasure Φ hΦ T hT).map (fun z => x + z)
  have hFc := (secondReconstructionGerm_contDiff v Y Z V (sourceAffineCoefficient v Y Z)
    Prod.snd C₂ hv hY hZ hV (sourceAffineCoefficient_contDiff v Y Z hv hY hZ) contDiff_snd).continuous
  have hec : Continuous (fun y => secondReconstructionGerm v Y Z V (sourceAffineCoefficient v Y Z)
      Prod.snd C₂ x y - v y * V y) := (hFc.comp (continuous_const.prodMk continuous_id)).sub (hv.continuous.mul hV.continuous)
  have hac : Continuous (fun y => (Y y - Y x) * V y - C₂) := hAc.comp (continuous_const.prodMk continuous_id)
  have hdc : Continuous (fun y => (Z y - Z x) * V y - 3 * C₂ * J y) := hDc.comp (continuous_const.prodMk continuous_id)
  have hxc (i : Fin 3) : Continuous (fun y : ParabolicSpace => (y.2 i - x.2 i) * V y) := by fun_prop
  have hei : Integrable (fun y => (1 : ℝ) * (secondReconstructionGerm v Y Z V (sourceAffineCoefficient v Y Z)
      Prod.snd C₂ x y - v y * V y)) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ hT hT₁.le x _ hec
  have hdi : Integrable (fun y => (1 : ℝ) * ((Z y - Z x) * V y - 3 * C₂ * J y)) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ hT hT₁.le x _ hdc
  have hai : Integrable (fun y => (1 : ℝ) * ((Y y - Y x) * V y - C₂)) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ hT hT₁.le x _ hac
  have hxi (i : Fin 3) : Integrable (fun y : ParabolicSpace => (1 : ℝ) * ((y.2 i - x.2 i) * V y)) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ hT hT₁.le x _ (hxc i)
  have hh := secondReconstructionGerm_product_bound μ (fun _ => 1) v J Y Z V (sourceAffineCoefficient v Y Z)
    Prod.snd C₂ x hei hdi hai hxi (by simpa only [one_mul, μ, integral_centered_measure _ x _ hec] using hrec)
    (by simpa only [one_mul, μ, integral_centered_measure _ x _ hdc] using hd)
    (by simpa only [one_mul, μ, integral_centered_measure _ x _ hac] using ha)
    hvx (fun i => (norm_le_pi_norm (sourceAffineCoefficient v Y Z x) i).trans hνx)
    (fun i => by simpa only [one_mul, μ, integral_centered_measure _ x _ (hxc i)] using hxtest i)
  have hpc : Continuous (fun y => (v y - v x) * V y + 3 * C₂ * (v y + J y)) := by fun_prop
  simpa only [one_mul, μ, integral_centered_measure _ x _ hpc, Fintype.card_fin, Nat.cast_ofNat] using hh

end GlobalPhi43.MW20
