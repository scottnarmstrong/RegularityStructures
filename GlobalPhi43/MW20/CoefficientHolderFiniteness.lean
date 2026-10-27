module

public import GlobalPhi43.MW20.ScalarHolderFiniteness
public import GlobalPhi43.MW20.SourceCoefficientNormTests

/-! Finiteness of the actual vector coefficient norm on bounded domains.
This uses smoothness of the selected diagonal derivative, without estimating
that norm by a radius-truncated norm or imposing an independent finite-norm premise. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Smooth spatial coefficient fields have finite local Holder norm. -/
theorem coefficientHolderSeminorm_finite_bound (ν : ParabolicSpace → Fin 3 → ℝ)
    (hν : ContDiff ℝ ∞ ν) (D : Set ParabolicSpace) (R : ℝ) (hD : D ⊆ Metric.closedBall 0 R)
    {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) :
    ∃ N : ℝ, 0 ≤ N ∧ localCoefficientHolderSeminorm ν D α ≤ ENNReal.ofReal N := by
  have hfinite (i : Fin 3) : ∃ N : ℝ, 0 ≤ N ∧
      scalarHolderSeminorm (fun x => ν x i) D α ≤ ENNReal.ofReal N :=
    scalarHolderSeminorm_finite_bound _ ((contDiff_apply ℝ ℝ i).comp hν) D R hD hα hα₁
  choose N hN hnorm using hfinite
  have hsum : 0 ≤ ∑ i, N i := Finset.sum_nonneg fun i _ => hN i
  refine ⟨∑ i, N i, hsum, ?_⟩
  unfold localCoefficientHolderSeminorm
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => iSup_le fun hne => ?_
  apply (ENNReal.ofReal_le_ofReal_iff hsum).2
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) _)).2
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsum (Real.rpow_nonneg (pdist_nonneg x y) _))).2
  intro i
  have hh := scalarHolderSeminorm_increment_bound (fun x => ν x i) D α (hN i) (hnorm i) hy hx
  rw [pdist_symm y x] at hh
  have hNi : N i ≤ ∑ j, N j := Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    hh.trans (mul_le_mul_of_nonneg_right hNi (Real.rpow_nonneg (pdist_nonneg x y) _))

/-- The source-selected optimal coefficient automatically has finite local
Holder norm at every source regularity between zero and one. -/
theorem sourceAffineCoefficient_holder_ne_top (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (D : Set ParabolicSpace) (R : ℝ) (hD : D ⊆ Metric.closedBall 0 R)
    {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) :
    localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D α ≠ ⊤ := by
  obtain ⟨N, _, hN⟩ := coefficientHolderSeminorm_finite_bound _
    (sourceAffineCoefficient_contDiff v Y Z hv hY hZ) D R hD hα hα₁
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hN

end GlobalPhi43.MW20
