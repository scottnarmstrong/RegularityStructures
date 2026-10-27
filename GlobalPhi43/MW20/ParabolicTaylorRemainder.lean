module

public import GlobalPhi43.MW20.CompactTaylorRemainder
public import GlobalPhi43.MW20.SpatialJetPairing
public import GlobalPhi43.MW20.SourceHolder

/-!
# Smooth source remainders are uniformly quadratic in the parabolic metric
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The smooth diagonal spatial coefficient leaves a quadratic parabolic
remainder on every compact ball. Ambient derivative constants prove only
finiteness; the actual seminorm still governs all quantitative source rows. -/
theorem parabolic_compact_remainder_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Metric.closedBall (0 : ParabolicSpace) R,
      ∀ y ∈ Metric.closedBall (0 : ParabolicSpace) R, Local.pdist x y ≤ 1 →
      |U (x, y) - U (x, x) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| ≤
        B * Local.pdist x y ^ 2 := by
  obtain ⟨K, hK⟩ := compact_ball_taylor_remainder U hU R
  have hDU : ContDiff ℝ ∞ (fderiv ℝ U) := hU.fderiv_right (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ParabolicSpace × ParabolicSpace) R).exists_bound_of_continuousOn hDU.continuous.continuousOn
  refine ⟨(K : ℝ) + max M 0, by positivity, ?_⟩
  intro x hx y hy hpd
  have hxN : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hyN : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hxx : (x, x) ∈ Metric.closedBall (0 : ParabolicSpace × ParabolicSpace) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] using max_le hxN hxN
  have hxy : (x, y) ∈ Metric.closedBall (0 : ParabolicSpace × ParabolicSpace) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] using max_le hxN hyN
  have hd : (x, y) - (x, x) = ((0 : ParabolicSpace), y - x) := by ext i <;> simp
  have ht := hK (x, x) hxx (x, y) hxy
  rw [hd] at ht
  have hdispNorm : ‖((0 : ParabolicSpace), y - x)‖ = ‖y - x‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg (y - x))]
  rw [hdispNorm, Real.norm_eq_abs] at ht
  have hn : ‖y - x‖ ≤ Local.pdist x y := by
    simpa only [norm_sub_rev] using norm_sub_le_pdist hpd
  have ht' := ht.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hn 2) K.coe_nonneg)
  have heunit : ‖((0 : ParabolicSpace), ((1 : ℝ), (0 : Fin 3 → ℝ)))‖ = 1 := by simp
  have hb : |fderiv ℝ U (x, x) (0, (1, 0))| ≤ max M 0 := by
    have hh := (fderiv ℝ U (x, x)).le_opNorm ((0 : ParabolicSpace), ((1 : ℝ), (0 : Fin 3 → ℝ)))
    have hb := (hM (x, x) hxx).trans (le_max_left M 0)
    have hh' : |fderiv ℝ U (x, x) (0, (1, 0))| ≤ ‖fderiv ℝ U (x, x)‖ := by
      simpa only [Real.norm_eq_abs, heunit, mul_one] using hh
    exact hh'.trans hb
  have htime : |y.1 - x.1| ≤ Local.pdist x y ^ 2 := by
    have hs : Real.sqrt |y.1 - x.1| ≤ Local.pdist x y := by
      simpa only [Local.pdist, abs_sub_comm] using (le_max_left (Real.sqrt |x.1 - y.1|) ‖x.2 - y.2‖)
    nlinarith [Real.sq_sqrt (abs_nonneg (y.1 - x.1)), Real.sqrt_nonneg |y.1 - x.1|,
      Local.pdist_nonneg x y]
  have hlin : |(y.1 - x.1) * fderiv ℝ U (x, x) (0, (1, 0))| ≤
      max M 0 * Local.pdist x y ^ 2 := by
    rw [abs_mul]
    have hh := mul_le_mul htime hb (abs_nonneg _) (sq_nonneg (Local.pdist x y))
    nlinarith only [hh]
  have he : U (x, y) - U (x, x) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i) =
      (U (x, y) - U (x, x) - fderiv ℝ U (x, x) (0, y - x)) +
        (y.1 - x.1) * fderiv ℝ U (x, x) (0, (1, 0)) := by
    rw [diagonal_derivative_split U hU x y]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by nlinarith only [ht', hlin])

end GlobalPhi43.MW20
