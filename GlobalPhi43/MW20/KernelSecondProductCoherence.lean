module

public import GlobalPhi43.MW20.KernelCenteredTesting
public import GlobalPhi43.MW20.KernelCoordinateSeminorm
public import GlobalPhi43.MW20.SourceCoefficientNormTests
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.SecondProductExponentSet

/-! The second product's source coherence attached to the actual MW20 kernel,
actual tree seminorms and the actual optimal diagonal derivative. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Source Lemma 2.10 coherence with its three distinct testing exponents. No
independent coefficient or optimality field is supplied by the caller. -/
theorem kernel_secondProduct_coherence_exponent_set (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    (D : Set ParabolicSpace) (hD : IsOpen D) {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 14)
    {a b : ParabolicSpace} (ha : a ∈ D) (hb : b ∈ D) (hne : b ≠ a)
    {t : ℝ} (ht : 0 < t) (ht₁ : t < 1)
    {Hv HU Hν NA NV NX : ℝ} (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν)
    (hNA : 0 ≤ NA) (hNV : 0 ≤ NV) (hNX : 0 ≤ NX)
    (hvnorm : scalarHolderSeminorm v D (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hUnorm : localAffineSeminorm (sourceExpansion v Y Z) D (3 / 2 - 5 * ε) ≤ ENNReal.ofReal HU)
    (hνnorm : localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D
      (1 / 2 - 5 * ε) ≤ ENNReal.ofReal Hν)
    (hAnorm : recenteredASeminorm (mw20TestingKernel Φ hΦ) D ε Y V C₂ ≤ ENNReal.ofReal NA)
    (hVnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D (-1 - 2 * ε) V ≤ ENNReal.ofReal NV)
    (hXnorm : recenteredXVSeminorm (mw20TestingKernel Φ hΦ) D ε V ≤ ENNReal.ofReal NX) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ t ht)
      (fun y => secondReconstructionGerm v Y Z V (sourceAffineCoefficient v Y Z)
        Prod.snd C₂ a y - secondReconstructionGerm v Y Z V (sourceAffineCoefficient v Y Z)
        Prod.snd C₂ b y) b| ≤
      ∑ β ∈ ({-4 * ε, -1 - 2 * ε, -2 * ε} : Finset ℝ),
        (if β = -4 * ε then 3 * Hv * NA else if β = -1 - 2 * ε then HU * NV else 3 * Hν * NX) *
          pdist a b ^ ((1 / 2 - 7 * ε) - β) * t ^ β := by
  let μ := (infiniteKernelMeasure Φ hΦ t ht).map (fun z => b + z)
  have hAc : Continuous (fun y => (Y y - Y b) * V y - C₂) := by fun_prop
  have hAi : Integrable (fun y => (1 : ℝ) * ((Y y - Y b) * V y - C₂)) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ ht ht₁.le b _ hAc
  have hVi : Integrable (fun y => (1 : ℝ) * V y) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ ht ht₁.le b V hV.continuous
  have hXc (i : Fin 3) : Continuous (fun y : ParabolicSpace => (y.2 i - b.2 i) * V y) := by fun_prop
  have hXi (i : Fin 3) : Integrable (fun y : ParabolicSpace => (1 : ℝ) * ((y.2 i - b.2 i) * V y)) μ := by
    simpa only [one_mul] using reconstruction_centered_integrable Φ hΦ ht ht₁.le b _ (hXc i)
  have htestA := recenteredASeminorm_test_bound (mw20TestingKernel Φ hΦ) D ε Y V C₂ hNA hAnorm hb ht ht₁
  have htestV := negativeTreeSeminorm_test_bound (mw20TestingKernel Φ hΦ) D (-1 - 2 * ε) V hNV hVnorm hb ht ht₁.le
  rw [mw20TestingKernel_pos Φ hΦ ht] at htestA htestV
  have htestX (i : Fin 3) := recenteredXVSeminorm_component_test_bound (mw20TestingKernel Φ hΦ) D ε V
    hNX hXnorm hb ht ht₁ (mw20_coordinateTree_integrable Φ hΦ V hV.continuous b ht ht₁.le) i
  have hvab := scalarHolderSeminorm_increment_bound v D (1 / 2 - 3 * ε) hHv hvnorm hb ha
  rw [pdist_symm b a] at hvab
  have hUab := source_affine_norm_remainder v Y Z hv hY hZ D hD (by linarith : 1 < 3 / 2 - 5 * ε)
    hHU hUnorm ha hb hne
  have hνab := source_coefficient_holder_component_bound (sourceAffineCoefficient v Y Z) D
    (1 / 2 - 5 * ε) hHν hνnorm ha hb hne
  have hh := secondReconstructionGerm_coherence_exponent_set μ (fun _ => 1) v Y Z V
    (sourceAffineCoefficient v Y Z) Prod.snd C₂ a b hAi hVi hXi hε hsmall hvab hUab hνab (by
      simpa only [one_mul, μ, integral_centered_measure _ b _ hAc] using htestA) (by
      simpa only [one_mul, μ, integral_centered_measure _ b _ hV.continuous] using htestV) (by
      intro i
      have hh := htestX i
      rw [mw20TestingKernel_pos Φ hΦ ht] at hh
      simpa only [one_mul, μ, integral_centered_measure _ b _ (hXc i)] using hh)
  have hFc := (secondReconstructionGerm_contDiff v Y Z V (sourceAffineCoefficient v Y Z)
    Prod.snd C₂ hv hY hZ hV (sourceAffineCoefficient_contDiff v Y Z hv hY hZ) contDiff_snd).continuous
  have hdiff : Continuous (fun y => secondReconstructionGerm v Y Z V (sourceAffineCoefficient v Y Z)
      Prod.snd C₂ a y - secondReconstructionGerm v Y Z V (sourceAffineCoefficient v Y Z) Prod.snd C₂ b y) :=
    (hFc.comp (continuous_const.prodMk continuous_id)).sub (hFc.comp (continuous_const.prodMk continuous_id))
  simpa only [one_mul, μ, integral_centered_measure _ b _ hdiff, Fintype.card_fin, Nat.cast_ofNat] using hh

end GlobalPhi43.MW20
