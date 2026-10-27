module

public import GlobalPhi43.MW20.AugmentedLargeScaleRow
public import GlobalPhi43.MW20.ClosingFirstSup
public import GlobalPhi43.MW20.ClosingSecondSup
public import GlobalPhi43.MW20.ClosingHolderError
public import GlobalPhi43.MW20.ClosingCommutatorError
public import GlobalPhi43.MW20.AugmentedLargeScaleNormalization
public import GlobalPhi43.MW20.SourceLargeScaleConstants
public import GlobalPhi43.MW20.SourceWForcingSup
public import GlobalPhi43.MW20.ForcingRootNormalization
public import GlobalPhi43.MW20.ReconstructionKernelTests

/-! (4.31) assembly with actual parent forcing and interpolation. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The actual source large-scale row from the same exact-d0 radius
allowance. No forcing, Holder, commutator or maximum-row callback is used. -/
theorem source_augmented_large_scale_row_from_radius_bound
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V W e : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (he : ContDiff ℝ ∞ e)
    (hPDE : ∀ z ∈ sourceCylinder 0,
      sourceHeat v z = -v z ^ 3 - 3 * (v z ^ 2 * J z) - 3 * (v z * V z) -
        W z - 9 * C₂ * (v z + J z) - e z)
    {r k ε c A R E₁ E₂ E₃ : ℝ}
    (hE₁ : 0 ≤ E₁) (hE₃ : 0 ≤ E₃)
    (he₁ : ∀ z ∈ sourceCylinder 0, |e z| ≤ E₁)
    (hdefect : Local.DefectSmall c (sourceSup v r) E₁ E₂ E₃) (hr : 0 ≤ r) (hk : 2 < k)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hMpos : 0 < sourceSup v r)
    (hR : r + 1 / sourceSup v r < R) (hR1 : R ≤ 1 / 2)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r (1 / sourceSup v r) ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (A * sourceSup v r))
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hc1 : c ≤ 1)
    (hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε)))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetW : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(3 / 2) - 3 * ε) W ≤ ENNReal.ofReal (c * sourceSup v r ^ (3 / 2 - 3 * ε))) :
    let M := sourceSup v r
    let α := (1 / 2 : ℝ) - 3 * ε
    sourceSup v R ≤ ((92 / 62 : ℝ) * sourceLargeScaleConstant ε A) *
      max (1 / (R - (r + 1 / M)))
        (max (M * k ^ (-α)) (max (M * k ^ (-α / 3))
          (M * (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ)))) := by
  let M := sourceSup v r
  let T := (1 / M) / k
  let d := (1 / M) * (k - 1) / k
  let S := r + 1 / M
  let α := (1 / 2 : ℝ) - 3 * ε
  have hS : r + 1 / sourceSup v r ≤ 1 / 2 := hR.le.trans hR1
  have hg := reciprocal_source_geometry hr hMpos hk hS
  dsimp only at hg
  let μ := infiniteKernelMeasure Φ hΦ T hg.1
  have hk0 : 0 < k := by linarith
  have hST : S - T = r + d := by
    dsimp [S, T, d]
    field_simp
    ring
  have hTS : T < S := by
    have hd : 0 < d := hg.2.2.1.1
    have : 0 < S - T := by rw [hST]; positivity
    linarith
  have hcont (f : ParabolicSpace → ℝ) (hf : Continuous f) :
      Continuous (pastSmooth (infiniteKernelMeasure Φ hΦ T hg.1) f) :=
    reconstruction_kernel_diagonal_test_continuous Φ hΦ hg.1 hg.2.1.le
      (fun p => f p.2) (hf.comp continuous_snd)
  have hF := source_first_forcing_sup_positive Φ hΦ v Y Z J hv hY hZ hJ hr hk hε hsmall hc hc1
    hA hMpos hS hnorm hbudgetY hbudgetZ hbudgetJ hbudgetB
  have hG := source_complete_second_forcing_sup_positive Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV hr hk
    hε hsmall hc hA hMpos hS hnorm hbudgetY hbudgetZ hc1 hbudgetA hbudgetV hbudgetX hbudgetD
  have hWf := source_W_forcing_sup Φ hΦ W hr hMpos hk hS hc hbudgetW
  have hSI : S ∈ Icc (0 : ℝ) (1 / 2) := ⟨by dsimp [S]; positivity, hS⟩
  have hFn := sourceSup_nonneg (hcont _ ((hv.continuous.pow 2).mul hJ.continuous)) hSI
  have hGn := sourceSup_nonneg
    ((hcont _ (hv.continuous.mul hV.continuous)).add
      (((hcont v hv.continuous).add (hcont J hJ.continuous)).const_mul (3 * C₂))) hSI
  have hWn := sourceSup_nonneg (hcont W hW.continuous) hSI
  have hFK := sourceFirstForcingConstant_nonneg hsmall hA
  have hGK := sourceSecondForcingConstant_nonneg hsmall hA
  have hPK := sourcePositiveErrorConstant_nonneg (ε := ε) hA
  change _ ≤ sourceFirstForcingConstant ε A * c * M ^ (3 : ℝ) * k ^ (3 / 2 + 3 * ε) at hF
  change _ ≤ sourceSecondForcingConstant ε A * c * M ^ (3 : ℝ) * k ^ (3 / 2 + 3 * ε) at hG
  have hFr := cubic_forcing_root_normalization hFn hFK hc hMpos hk0 hF
  have hGr := cubic_forcing_root_normalization hGn hGK hc hMpos hk0 hG
  have hWr := cubic_forcing_root_normalization hWn (by norm_num : (0 : ℝ) ≤ 1) hc hMpos hk0
    (by simpa only [one_mul] using hWf)
  rw [Real.one_rpow] at hWr
  have hER : r + (1 / sourceSup v r) * (k - 1) / k ≤ R - T := by
    change r + d ≤ R - T
    rw [← hST]
    linarith
  have hE := source_holder_testing_error_positive v Y Z hv hY hZ hr hk hε hsmall hc hc1 hA hMpos hS hER
    hnorm hbudgetY hbudgetZ
  have hP := source_commutator_parent_error_positive v Y Z hv hY hZ hr hk hε hsmall hc hc1 hA hMpos hS
    hnorm hbudgetY hbudgetZ
  have hreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hrow := mw20_augmented_row_4_31 Φ hΦ hreg hJ.continuous.continuousOn hV.continuous.continuousOn
    hW.continuous.continuousOn he.continuous.continuousOn C₂ hPDE he₁ (by dsimp [α]; linarith : 0 ≤ α)
    (by dsimp [α]; linarith : α ≤ 1) hg.1 hTS hR hR1
  rw [hST] at hrow
  have hCE : sourceHolder v α (R - T) (2 * T) * T ^ α ≤ sourcePositiveErrorConstant ε A * (M * k ^ (-α)) := by
    convert hE using 1; dsimp only [M, T, α, sourcePositiveErrorConstant]; ring
  have hCP : cubicCommutatorScale (sourceSup v (r + d))
      (sourceHolder v α (r + d) (2 * T)) T α ≤ sourcePositiveErrorConstant ε A ^ (1 / 3 : ℝ) * (M * k ^ (-α / 3)) := by
    convert hP using 1; dsimp only [M, T, d, α, sourcePositiveErrorConstant]; ring
  have hCF : sourceSup (pastSmooth μ (fun y => v y ^ 2 * J y)) S ^ (1 / 3 : ℝ) ≤ sourceFirstForcingConstant ε A ^ (1 / 3 : ℝ) *
      (M * (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ)) := by convert hFr using 1; ring
  have hCG : sourceSup (fun x => pastSmooth μ (fun y => v y * V y) x +
      3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x)) S ^ (1 / 3 : ℝ) ≤ sourceSecondForcingConstant ε A ^ (1 / 3 : ℝ) *
      (M * (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ)) := by convert hGr using 1; ring
  have hCW : sourceSup (pastSmooth μ W) S ^ (1 / 3 : ℝ) ≤ (1 : ℝ) * (M * (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ)) := by
    simpa only [one_mul] using hWr
  have hdef := augmented_defect_root_normalization hc hMpos.le hE₁ hE₃ hdefect hk hε
  have hCW' : max (sourceSup (pastSmooth μ W) S ^ (1 / 3 : ℝ)) (E₁ ^ (1 / 3 : ℝ)) ≤
      (1 : ℝ) * (M * (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ)) :=
    max_le hCW (by simpa only [one_mul] using hdef)
  have hn := normalize_augmented_large_scale_maximum (one_div_nonneg.mpr (sub_nonneg.mpr hR.le)) hPK
    (Real.rpow_nonneg hPK _) (Real.rpow_nonneg hFK _) (Real.rpow_nonneg hGK _)
    (by norm_num) hCE hCP hCF hCG hCW' hrow
  convert hn using 1
  dsimp only [sourceLargeScaleConstant]
  ring

end GlobalPhi43.MW20
