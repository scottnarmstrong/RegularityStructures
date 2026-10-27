module

public import GlobalPhi43.MW20.KernelFirstReconstruction
public import GlobalPhi43.MW20.FirstProductAssembly
public import GlobalPhi43.MW20.SourceNormDomains

/-! Complete first-product assembly: reconstruction and both local
terms are derived from source norms and the actual constructed MW20 kernel. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- First product with an explicit reconstruction budget and the two
literal local terms. No reconstruction-error input is assumed. -/
theorem kernel_firstProduct_product_bound (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v) (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    (x : ParabolicSpace) {T ε : ℝ} (hT : 0 < T) (hT₁ : T < 1)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14)
    {M H Hv HZ NJ NB : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHZ : 0 ≤ HZ)
    (hNJ : 0 ≤ NJ) (hNB : 0 ≤ NB) (hsup : ∀ a ∈ pastBall x T, |v a| ≤ M)
    (hplus : scalarHolderSeminorm (fun y => v y + Z y) (pastBall x T) (1 - 2 * ε) ≤ ENNReal.ofReal H)
    (hvnorm : scalarHolderSeminorm v (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hZnorm : scalarHolderSeminorm Z (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal HZ)
    (hJnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) (-(1 / 2) - ε) J ≤ ENNReal.ofReal NJ)
    (hBnorm : recenteredBSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε Z J ≤ ENNReal.ofReal NB) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => v y ^ 2 * J y) x| ≤
      ((2 * M * H * NJ * (2 * T) ^ (4 * ε) + Hv * HZ * NJ) * T ^ (1 / 2 - 7 * ε) +
        (2 * Hv * NB) * T ^ (1 / 2 - 7 * ε)) / (1 - (1 / 2 : ℝ) ^ (1 / 2 - 7 * ε)) +
      M ^ 2 * (NJ * T ^ (-(1 / 2) - ε)) + 2 * M * (NB * T ^ (-4 * ε)) := by
  have hrec := kernel_firstProduct_reconstruction Φ hΦ v Z J hv hZ hJ x hT hT₁ hε hsmall
    hM hH hHv hHZ hNJ hNB hsup hplus hvnorm hZnorm hJnorm hBnorm
  have hx : x ∈ closure (pastBall x T) := reconstruction_mem_closure_pastBall x x hT
    (by simpa only [pdist, sub_self, abs_zero, Real.sqrt_zero, norm_zero, max_self] using hT.le) le_rfl
  have hvx := source_sup_bound_closure v hv.continuous (pastBall x T) hsup hx
  have hJclosure : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) (closure (pastBall x T))
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal NJ := by
    unfold negativeTreeSeminorm
    rw [mw20_localTestSeminorm_closure Φ hΦ (pastBall x T) (Ioc 0 1) (fun _ h => h)
      (-(1 / 2) - ε) (fun p => J p.2) (hJ.continuous.comp continuous_snd)]
    exact hJnorm
  have hBG : Continuous (fun p : ParabolicSpace × ParabolicSpace => (Z p.2 - Z p.1) * J p.2) := by fun_prop
  have hBclosure : recenteredBSeminorm (mw20TestingKernel Φ hΦ) (closure (pastBall x T)) ε Z J ≤ ENNReal.ofReal NB := by
    unfold recenteredBSeminorm
    rw [mw20_localTestSeminorm_closure Φ hΦ (pastBall x T) (Ioo 0 1) (fun _ h => ⟨h.1, h.2.le⟩)
      (-4 * ε) (fun p => (Z p.2 - Z p.1) * J p.2) hBG]
    exact hBnorm
  have hj := negativeTreeSeminorm_test_bound (mw20TestingKernel Φ hΦ) (closure (pastBall x T))
    (-(1 / 2) - ε) J hNJ hJclosure hx hT hT₁.le
  have hb := recenteredBSeminorm_reversed_test_bound (mw20TestingKernel Φ hΦ) (closure (pastBall x T))
    ε Z J hNB hBclosure hx hT hT₁
  rw [mw20TestingKernel_pos Φ hΦ hT] at hj hb
  let μ := (infiniteKernelMeasure Φ hΦ T hT).map (fun z => x + z)
  have hp : Continuous (fun y => v y ^ 2 * J y) := (hv.continuous.pow 2).mul hJ.continuous
  have hbc : Continuous (fun y => (Z x - Z y) * J y) := (continuous_const.sub hZ.continuous).mul hJ.continuous
  have hFc := (firstProductGerm_contDiff v Z J hv hZ hJ).continuous
  have hec : Continuous (fun y => firstProductGerm v Z J x y - v y ^ 2 * J y) :=
    (hFc.comp (continuous_const.prodMk continuous_id)).sub hp
  have hPi : Integrable (fun y => (1 : ℝ) * (v y ^ 2 * J y)) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ hT hT₁.le x _ hp
  have hJi : Integrable (fun y => (1 : ℝ) * J y) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ hT hT₁.le x J hJ.continuous
  have hBi : Integrable (fun y => (1 : ℝ) * ((Z x - Z y) * J y)) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ hT hT₁.le x _ hbc
  have hh := firstProductGerm_product_bound μ (fun _ => 1) v Z J x hPi hJi hBi (by
      simpa only [one_mul, μ, integral_centered_measure _ x _ hec] using hrec)
    hvx (by simpa only [one_mul, μ, integral_centered_measure _ x J hJ.continuous] using hj)
    (by simpa only [one_mul, μ, integral_centered_measure _ x _ hbc] using hb)
  simpa only [one_mul, μ, integral_centered_measure _ x _ hp] using hh

end GlobalPhi43.MW20
