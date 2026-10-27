module

public import GlobalPhi43.MW20.KernelCenteredTesting
public import GlobalPhi43.MW20.FirstProductExponentSet
public import GlobalPhi43.MW20.ScalarHolderSeminorm

/-! The first product's tested coherence bound attached to the actual MW20
kernel and actual local scalar/tree seminorms. The tree factor J is retained. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- First-product coherence, with all testing and scalar increments
extracted from their actual seminorms. Source continuity supplies integrability. -/
theorem kernel_firstProduct_coherence_scales (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v) (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    (D : Set ParabolicSpace) (ε : ℝ) (a b : ParabolicSpace) (ha : a ∈ D) (hb : b ∈ D)
    {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) (hab : 0 < pdist a b)
    {M H Hv HZ NJ NB : ℝ} (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHZ : 0 ≤ HZ)
    (hNJ : 0 ≤ NJ) (hNB : 0 ≤ NB) (hva : |v a| ≤ M) (hvb : |v b| ≤ M)
    (hplus : scalarHolderSeminorm (fun y => v y + Z y) D (1 - 2 * ε) ≤ ENNReal.ofReal H)
    (hvnorm : scalarHolderSeminorm v D (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hZnorm : scalarHolderSeminorm Z D (1 / 2 - 3 * ε) ≤ ENNReal.ofReal HZ)
    (hJnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D (-(1 / 2) - ε) J ≤ ENNReal.ofReal NJ)
    (hBnorm : recenteredBSeminorm (mw20TestingKernel Φ hΦ) D ε Z J ≤ ENNReal.ofReal NB) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ t ht)
      (fun y => firstProductGerm v Z J a y - firstProductGerm v Z J b y) b| ≤
      2 * M * H * NJ * pdist a b ^ (1 - 2 * ε) * t ^ (-(1 / 2) - ε) +
      Hv * HZ * NJ * pdist a b ^ (1 - 6 * ε) * t ^ (-(1 / 2) - ε) +
      2 * Hv * NB * pdist a b ^ (1 / 2 - 3 * ε) * t ^ (-4 * ε) := by
  let ν := (infiniteKernelMeasure Φ hΦ t ht).map (fun z => b + z)
  have hJint : Integrable J ν := reconstruction_centered_integrable Φ hΦ ht ht₁.le b J hJ.continuous
  have hBcont : Continuous (fun y => (Z b - Z y) * J y) := (continuous_const.sub hZ.continuous).mul hJ.continuous
  have hBint : Integrable (fun y => (Z b - Z y) * J y) ν :=
    reconstruction_centered_integrable Φ hΦ ht ht₁.le b _ hBcont
  have htestJ := negativeTreeSeminorm_test_bound (mw20TestingKernel Φ hΦ) D
    (-(1 / 2) - ε) J hNJ hJnorm hb ht ht₁.le
  have htestB := recenteredBSeminorm_reversed_test_bound (mw20TestingKernel Φ hΦ) D ε Z J
    hNB hBnorm hb ht ht₁
  rw [mw20TestingKernel_pos Φ hΦ ht] at htestJ htestB
  have hiJ : Integrable (fun y => (1 : ℝ) * J y) ν := by simpa only [one_mul] using hJint
  have hiB : Integrable (fun y => (1 : ℝ) * ((Z b - Z y) * J y)) ν := by
    simpa only [one_mul] using hBint
  have hplusab := scalarHolderSeminorm_increment_bound _ D (1 - 2 * ε) hH hplus hb ha
  have hvab := scalarHolderSeminorm_increment_bound v D (1 / 2 - 3 * ε) hHv hvnorm hb ha
  have hZab := scalarHolderSeminorm_increment_bound Z D (1 / 2 - 3 * ε) hHZ hZnorm hb ha
  rw [pdist_symm b a] at hplusab hvab hZab
  have hh := firstProductGerm_coherence_scales ν (fun _ => 1) v Z J a b hiJ hiB hab
    hva hvb hplusab hvab hZab (by
      simpa only [one_mul, ν, integral_centered_measure _ b J hJ.continuous] using htestJ) (by
      simpa only [one_mul, ν, integral_centered_measure _ b _ hBcont] using htestB)
  have hFcont : Continuous (fun y => firstProductGerm v Z J a y - firstProductGerm v Z J b y) := by
    have hc := (firstProductGerm_contDiff v Z J hv hZ hJ).continuous
    exact (hc.comp (continuous_const.prodMk continuous_id)).sub
      (hc.comp (continuous_const.prodMk continuous_id))
  simpa only [one_mul, ν, integral_centered_measure _ b _ hFcont] using hh

/-- First-product coherence indexed by the literal two-element testing
exponent set; zero source seminorms remain zero. -/
theorem kernel_firstProduct_coherence_exponent_set (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v) (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    (D : Set ParabolicSpace) (ε : ℝ) (a b : ParabolicSpace) (ha : a ∈ D) (hb : b ∈ D)
    {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) (hab : 0 < pdist a b)
    {M H Hv HZ NJ NB : ℝ} (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHZ : 0 ≤ HZ)
    (hNJ : 0 ≤ NJ) (hNB : 0 ≤ NB) (hva : |v a| ≤ M) (hvb : |v b| ≤ M)
    (hplus : scalarHolderSeminorm (fun y => v y + Z y) D (1 - 2 * ε) ≤ ENNReal.ofReal H)
    (hvnorm : scalarHolderSeminorm v D (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hZnorm : scalarHolderSeminorm Z D (1 / 2 - 3 * ε) ≤ ENNReal.ofReal HZ)
    (hJnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D (-(1 / 2) - ε) J ≤ ENNReal.ofReal NJ)
    (hBnorm : recenteredBSeminorm (mw20TestingKernel Φ hΦ) D ε Z J ≤ ENNReal.ofReal NB)
    {R : ℝ} (hR : pdist a b ≤ R) (hε : 0 ≤ ε) (hsmall : ε < 1 / 14) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ t ht)
      (fun y => firstProductGerm v Z J a y - firstProductGerm v Z J b y) b| ≤
      ∑ β ∈ ({-(1 / 2 : ℝ) - ε, -4 * ε} : Finset ℝ),
        (if β = -(1 / 2) - ε then 2 * M * H * NJ * R ^ (4 * ε) + Hv * HZ * NJ
          else 2 * Hv * NB) * pdist a b ^ ((1 / 2 - 7 * ε) - β) * t ^ β := by
  classical
  have hne : -(1 / 2 : ℝ) - ε ≠ -4 * ε := by intro he; linarith
  have hbase := kernel_firstProduct_coherence_scales Φ hΦ v Z J hv hZ hJ D ε a b ha hb
    ht ht₁ hab hH hHv hHZ hNJ hNB hva hvb hplus hvnorm hZnorm hJnorm hBnorm
  have hM : 0 ≤ M := (abs_nonneg (v a)).trans hva
  have hmerged := merge_repeated_test_exponent (d := pdist a b) (R := R)
    (t := t) (a₁ := 1 - 2 * ε) (a₂ := 1 - 6 * ε)
    (b := -(1 / 2) - ε) (a₃ := 1 / 2 - 3 * ε) (c := -4 * ε)
    (C₁ := 2 * M * H * NJ) (C₂ := Hv * HZ * NJ) (C₃ := 2 * Hv * NB)
    hab hR ht.le (by linarith) (by positivity)
  have he₁ : (1 - 2 * ε) - (1 - 6 * ε) = 4 * ε := by ring
  have he₂ : (1 / 2 - 7 * ε) - (-(1 / 2) - ε) = 1 - 6 * ε := by ring
  have he₃ : (1 / 2 - 7 * ε) - -4 * ε = 1 / 2 - 3 * ε := by ring
  simpa only [Finset.sum_pair hne, eq_self, ite_true, Ne.symm hne, ite_false, he₁, he₂, he₃] using
    hbase.trans hmerged

end GlobalPhi43.MW20
