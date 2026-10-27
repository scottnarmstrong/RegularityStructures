module

public import GlobalPhi43.MW20.ParabolicTaylorRemainder
public import GlobalPhi43.MW20.AffineSeminorm

/-!
# Finite smooth affine remainders on bounded source domains
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Smooth diagonal remainders have a finite parabolic Holder budget on any
bounded ball for 0≤γ≤2. The budget is only a finiteness witness. -/
theorem parabolic_affine_remainder_finite_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U) (R : ℝ)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall (0 : ParabolicSpace) R,
      ∀ y ∈ Metric.closedBall (0 : ParabolicSpace) R,
      |U (x, y) - U (x, x) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| ≤
        C * Local.pdist x y ^ γ := by
  obtain ⟨B, hB, hnear⟩ := parabolic_compact_remainder_bound U hU R
  let q : ParabolicSpace × ParabolicSpace → ℝ := fun p => U p - U (p.1, p.1) -
    ∑ i, diagonalSpatialCoefficient U p.1 i * (p.2.2 i - p.1.2 i)
  have hc : Continuous q := by
    have hcu := hU.continuous
    have hcv := (diagonalSpatialCoefficient_contDiff U hU).continuous
    dsimp only [q]
    fun_prop
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ParabolicSpace × ParabolicSpace) R).exists_bound_of_continuousOn hc.continuousOn
  let C := max B (max M 0)
  have hC : 0 ≤ C := hB.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hp : 0 ≤ Local.pdist x y := Local.pdist_nonneg x y
  by_cases hn : Local.pdist x y ≤ 1
  · by_cases he : y = x
    · subst y
      simp only [sub_self, mul_zero, Finset.sum_const_zero, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (Local.pdist_nonneg x x) γ)
    · have hp' := pdist_pos_of_ne he
      have hpow : Local.pdist x y ^ (2 : ℕ) ≤ Local.pdist x y ^ γ := by
        simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hp' hn hγ2
      exact (hnear x hx y hy hn).trans (mul_le_mul (le_max_left _ _) hpow (sq_nonneg _) hC)
  · have hxy : (x, y) ∈ Metric.closedBall (0 : ParabolicSpace × ParabolicSpace) R := by
      have hxN : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      have hyN : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] using max_le hxN hyN
    have hq : |U (x, y) - U (x, x) -
        ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| ≤ max M 0 := by
      simpa only [q, Real.norm_eq_abs] using (hM (x, y) hxy).trans (le_max_left M 0)
    have hpow := Real.one_le_rpow (le_of_not_ge hn) hγ
    exact hq.trans ((le_max_right B (max M 0)).trans (le_mul_of_one_le_right hC hpow))

end GlobalPhi43.MW20
