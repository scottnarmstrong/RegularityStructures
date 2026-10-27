module

public import GlobalPhi43.MW20.LocalPositiveInnerForcing

/-! Pricing the actual formal forcing average at the original d0-weighted
radius norm. No augmented or zero-defect PDE is an input. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_formal_forcing_weighted_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    {r d d₀ T L ε c : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : 0 < d) (hdd : d ≤ d₀) (hT : 0 < T)
    (hTL : T ≤ L) (hLd : L ≤ d / 8) (hε : 0 < ε) (hsmall : ε < 1 / 14)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hbudgetY : parabolicHolderSeminorm (1 - 2*ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c*sourceSup v r^(1 - 2*ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε)))
    (hMpos : 0 < sourceSup v r) (hscale : d₀*sourceSup v r ≤ 1)
    {x : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
 :
    let Q := localScalarSup (sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x) (Local.pastBall x L)
    let γ := (3 / 2 : ℝ)-5*ε
    let S := (Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal
    Q ≠ ⊤ ∧ d^γ*(T^2*Q.toReal) ≤
      ((4 : ℝ)^γ * sourceOnePointUniformBudget ε (sourceSup v r) S c)*
        (∑ a ∈ sourceSchauderExponents ε, T^a * L^(γ-a)) := by
  have hi := source_formal_one_point_inner_positive Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV
    hr hd hT hTL hLd hε hsmall hc hc1
    hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD hx
  have hscaleD : d*sourceSup v r ≤ 1 :=
    (mul_le_mul_of_nonneg_right hdd hMpos.le).trans hscale
  have hb := sourceOnePointCoefficient_inner_weighted_radius_positive v Y Z hv hY hZ
    hr hr1 hd hdd (hT.le.trans hTL) hLd hε hsmall hc hc1 ⟨x,hx⟩
    hbudgetY hbudgetZ hMpos hscaleD
  refine ⟨hi.1, ?_⟩
  have hR : 0 ≤ ∑ a ∈ sourceSchauderExponents ε,
      T^a*L^(((3 / 2 : ℝ)-5*ε)-a) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (Real.rpow_nonneg hT.le _)
      (Real.rpow_nonneg (hT.le.trans hTL) _)
  exact (mul_le_mul_of_nonneg_left hi.2 (Real.rpow_nonneg hd.le _)).trans
    (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hb hR)

end GlobalPhi43.MW20
