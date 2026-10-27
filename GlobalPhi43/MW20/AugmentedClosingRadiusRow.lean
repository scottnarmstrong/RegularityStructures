module

public import GlobalPhi43.MW20.AugmentedLargeScaleRadiusRow
public import GlobalPhi43.MW20.ParentClosingParameters

/-! The augmented local-positive parent-amplitude closing row after uniform k-then-c choice. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- [MW20, (4.33)] under an explicit radius bound at cutoff d0. The scale
and smallness cap are selected before the source fields and counterterms.
The radius bound is a hypothesis; the other analytic estimates, including
the defect-bearing maximum, follow from the source data. -/
theorem exists_source_augmented_closing_row_from_radius_bound {ε A cPrior : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hA : 0 ≤ A) (hPrior : 0 < cPrior) :
    ∃ k : ℝ, 2 < k ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ cPrior ∧ c₀ ≤ 1 ∧ ∀
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V W e : ParabolicSpace → ℝ) (C₂ : ℝ)
    (_ : ContDiff ℝ ∞ v) (_ : ContDiff ℝ ∞ J) (_ : ContDiff ℝ ∞ Y)
    (_ : ContDiff ℝ ∞ Z) (_ : ContDiff ℝ ∞ V) (_ : ContDiff ℝ ∞ W)
    (_ : ContDiff ℝ ∞ e)
    (_ : ∀ z ∈ sourceCylinder 0,
      sourceHeat v z = -v z ^ 3 - 3 * (v z ^ 2 * J z) - 3 * (v z * V z) -
        W z - 9 * C₂ * (v z + J z) - e z)
    (r R c E₁ E₂ E₃ : ℝ) (_ : 0 ≤ r)
    (_ : 0 ≤ E₁) (_ : 0 ≤ E₃)
    (_ : ∀ z ∈ sourceCylinder 0, |e z| ≤ E₁)
    (_ : Local.DefectSmall c (sourceSup v r) E₁ E₂ E₃)
    (_ : 0 ≤ c) (_ : 0 < sourceSup v r)
    (_ : r + 1 / sourceSup v r < R) (_ : R ≤ 1 / 2)
    (_ : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r (1 / sourceSup v r) ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (A * sourceSup v r))
    (_ : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (_ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (_ : c ≤ c₀)
    (_ : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (_ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (_ : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (_ : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε)))
    (_ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (_ : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (_ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(3 / 2) - 3 * ε) W ≤ ENNReal.ofReal (c * sourceSup v r ^ (3 / 2 - 3 * ε))),
    sourceSup v R ≤ max
      (((92 / 62 : ℝ) * sourceLargeScaleConstant ε A) / (R - (r + 1 / sourceSup v r))) (sourceSup v r / 2) := by
  obtain ⟨k, hk, c₀, hc₀, hcPrior, hc₀1, hclose⟩ := exists_parent_closing_parameters
    (C := (92 / 62 : ℝ) * sourceLargeScaleConstant ε A)
    hsmall (mul_nonneg (by norm_num) (sourceLargeScaleConstant_nonneg hsmall hA)) hPrior
  refine ⟨k, hk, c₀, hc₀, hcPrior, hc₀1, ?_⟩
  intro Φ hΦ v J Y Z V W e C₂ hv hJ hY hZ hV hW he hPDE r R c E₁ E₂ E₃ hr hE₁ hE₃ he₁ hdefect hc hMpos
    hR hR1 hnorm hbudgetY hbudgetZ hcc hbudgetA hbudgetV hbudgetX hbudgetD hbudgetJ hbudgetB hbudgetW
  have hrow := source_augmented_large_scale_row_from_radius_bound Φ hΦ v J Y Z V W e C₂ hv hJ hY hZ hV hW he hPDE
    hE₁ hE₃ he₁ hdefect hr hk hε hsmall hc hA hMpos hR hR1 hnorm hbudgetY hbudgetZ (hcc.trans hc₀1)
    hbudgetA hbudgetV hbudgetX hbudgetD hbudgetJ hbudgetB hbudgetW
  dsimp only at hrow
  have ha : -((1 / 2 : ℝ) - 3 * ε) = -1 / 2 + 3 * ε := by ring
  have hb : -((1 / 2 : ℝ) - 3 * ε) / 3 = -1 / 6 + ε := by ring
  rw [hb, ha] at hrow
  have hfinal := hclose c hc hcc (sourceSup v R) (sourceSup v r)
    (1 / (R - (r + 1 / sourceSup v r))) hMpos.le hrow
  simpa only [div_eq_mul_inv, mul_one, one_mul] using hfinal

end GlobalPhi43.MW20
