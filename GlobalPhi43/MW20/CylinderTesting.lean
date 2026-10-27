module

public import GlobalPhi43.MW20.KernelPastSupport
public import GlobalPhi43.MW20.CylinderSup
public import GlobalPhi43.Local.SmoothingComparison

/-!
# Exact cylinder containment for the MW20 kernel tests
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- Testing at a point of P_R by a closed-past radius-T kernel stays in
P_(R-T). This uses the exact max metric, including its time component. -/
theorem sourceCylinder_add_closedPast {R T : ℝ} (hT : 0 ≤ T) (hTR : T ≤ R)
    {x y : ParabolicSpace} (hx : x ∈ sourceCylinder R)
    (hyt : y.1 ≤ 0) (hy : Local.pdist 0 y ≤ T) :
    x + y ∈ sourceCylinder (R - T) := by
  have ht : Real.sqrt |y.1| ≤ T := by
    exact (le_max_left _ _).trans (by simpa only [Local.pdist, Prod.fst_zero,
      Prod.snd_zero, zero_sub, abs_neg, norm_neg] using hy)
  have hs : ‖y.2‖ ≤ T := by
    exact (le_max_right _ _).trans (by simpa only [Local.pdist, Prod.fst_zero,
      Prod.snd_zero, zero_sub, abs_neg, norm_neg] using hy)
  have hysq : |y.1| ≤ T ^ 2 := by
    nlinarith [Real.sq_sqrt (abs_nonneg y.1), Real.sqrt_nonneg |y.1|]
  change (R - T) ^ 2 < x.1 + y.1 ∧ x.1 + y.1 < 1 ∧
    ∀ i, |x.2 i + y.2 i| < 1 - (R - T)
  refine ⟨?_, by linarith [hx.2.1], ?_⟩
  · have htneg := (abs_le.mp hysq).1
    nlinarith [hx.1, mul_nonneg hT (sub_nonneg.mpr hTR)]
  · intro i
    have hi : |y.2 i| ≤ T := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y.2 i).trans hs
    exact (abs_add_le _ _).trans_lt (by linarith [hx.2.2 i])

/-- The actual infinite measure tests only points of the required larger
cylinder, with no radius enlargement or time-order assumption. -/
theorem infiniteKernelMeasure_ae_sourceCylinder (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {T R : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTR : T ≤ R) {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT, x + y ∈ sourceCylinder (R - T) := by
  filter_upwards [infiniteKernelMeasure_ae_closedPast Φ hΦ hT hT1] with y hy
  exact sourceCylinder_add_closedPast hT.le hTR hx hy.1 hy.2

end GlobalPhi43.MW20
