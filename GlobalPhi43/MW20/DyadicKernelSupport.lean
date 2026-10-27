module

public import GlobalPhi43.MW20.DyadicKernelMeasure
public import GlobalPhi43.Local.RadiusGeometry

/-!
# Local support of the actual finite MW20 kernels

The bounds use MW20's max parabolic distance, without changing to an
equivalent distance (which would cost constants depending on exponents).
The measure hypotheses apply in particular to the paper's smooth probability
 density supported in the unit past ball. No infinite kernel is assumed here.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local

private theorem measurable_pdist_zero : Measurable (pdist 0) := by
  unfold pdist
  fun_prop

/-- Exact dilation in the max distance used by MW20. -/
theorem pdist_zero_dilate (c : ℝ) (z : ParabolicSpace) :
    pdist 0 (parabolicDilate c z) = |c| * pdist 0 z := by
  simp only [pdist, parabolicDilate, Prod.fst_zero, Prod.snd_zero,
    zero_sub, abs_neg, norm_neg, abs_mul, abs_pow, norm_smul, Real.norm_eq_abs]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (abs_nonneg c), mul_max_of_nonneg _ _ (abs_nonneg c)]

/-- The max distance is subadditive for space-time displacements. -/
theorem pdist_zero_add (z w : ParabolicSpace) :
    pdist 0 (z + w) ≤ pdist 0 z + pdist 0 w := by
  have h := pdist_triangle 0 z (z + w)
  simpa only [pdist, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, zero_sub, sub_add_cancel_left,
    abs_neg, norm_neg] using h

/-- Addition of independent past-supported increments adds their support radii. -/
theorem conv_ae_past_radius (μ ν : Measure ParabolicSpace) [SFinite ν]
    {a b : ℝ}
    (hμ : ∀ᵐ z ∂μ, z.1 ≤ 0 ∧ pdist 0 z ≤ a)
    (hν : ∀ᵐ z ∂ν, z.1 ≤ 0 ∧ pdist 0 z ≤ b) :
    ∀ᵐ z ∂μ.conv ν, z.1 ≤ 0 ∧ pdist 0 z ≤ a + b := by
  rw [Measure.conv, ae_map_iff (by fun_prop) (by
    exact (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_pdist_zero measurable_const))]
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (measurableSet_le (measurable_fst.comp measurable_add) measurable_const).inter
      (measurableSet_le (measurable_pdist_zero.comp measurable_add) measurable_const))).mpr
  filter_upwards [hμ] with z hz
  filter_upwards [hν] with w hw
  exact ⟨add_nonpos hz.1 hw.1, (pdist_zero_add z w).trans (add_le_add hz.2 hw.2)⟩

/-- Each actual dyadic factor has its own exact past support radius. -/
theorem dyadicKernelFactor_ae_past_radius (μ : Measure ParabolicSpace)
    {T : ℝ} (hT : 0 ≤ T) (j : ℕ)
    (hμ : ∀ᵐ z ∂μ, z.1 ≤ 0 ∧ pdist 0 z ≤ 1) :
    ∀ᵐ z ∂dyadicKernelFactor μ T j,
      z.1 ≤ 0 ∧ pdist 0 z ≤ T / 2 ^ (j + 1) := by
  unfold dyadicKernelFactor
  rw [ae_map_iff (by unfold parabolicDilate; fun_prop) (by
    exact (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_pdist_zero measurable_const))]
  filter_upwards [hμ] with z hz
  have hc : 0 ≤ T / (2 : ℝ) ^ (j + 1) := by positivity
  refine ⟨mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hz.1, ?_⟩
  rw [pdist_zero_dilate, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left hz.2 hc).trans_eq (mul_one _)

/-- The finite convolution measure is supported at radius `T (1 - 2⁻ⁿ)`,
the radius obtained by summing the supports of its convolution factors. -/
theorem dyadicKernelMeasure_ae_past_radius (μ : Measure ParabolicSpace)
    [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 ≤ T)
    (hμ : ∀ᵐ z ∂μ, z.1 ≤ 0 ∧ pdist 0 z ≤ 1) (n : ℕ) :
    ∀ᵐ z ∂dyadicKernelMeasure μ T n,
      z.1 ≤ 0 ∧ pdist 0 z ≤ T * (1 - 1 / 2 ^ n) := by
  induction n with
  | zero => simp [dyadicKernelMeasure, kernelMeasure, pdist]
  | succ n ih =>
    have h := conv_ae_past_radius _ _ ih
      (dyadicKernelFactor_ae_past_radius μ hT n hμ)
    have heq : T * (1 - 1 / (2 : ℝ) ^ n) + T / 2 ^ (n + 1) =
        T * (1 - 1 / 2 ^ (n + 1)) := by
      rw [pow_succ]
      field_simp
      ring
    rw [heq] at h
    simpa only [dyadicKernelMeasure, kernelMeasure_succ, Nat.zero_add] using h

/-- Convert a support radius to the ambient norm only for topological limits.
The exponent-sensitive reconstruction estimates keep the max distance. -/
theorem norm_le_of_pdist_zero_le {z : ParabolicSpace} {r : ℝ}
    (hr : 0 ≤ r) (hz : pdist 0 z ≤ r) : ‖z‖ ≤ max (r ^ 2) r := by
  have ht : Real.sqrt |z.1| ≤ r := by
    simpa only [pdist, Prod.fst_zero, zero_sub, abs_neg] using
      (le_max_left _ _).trans hz
  have hs : ‖z.2‖ ≤ r := by
    simpa only [pdist, Prod.snd_zero, zero_sub, norm_neg] using
      (le_max_right _ _).trans hz
  have ht' : |z.1| ≤ r ^ 2 := by
    nlinarith [Real.sq_sqrt (abs_nonneg z.1), Real.sqrt_nonneg |z.1|]
  rw [Prod.norm_def, Real.norm_eq_abs]
  exact max_le_max ht' hs

/-- All truncations are supported in one fixed compact ambient ball. -/
theorem dyadicKernelMeasure_ae_norm_le (μ : Measure ParabolicSpace)
    [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 ≤ T)
    (hμ : ∀ᵐ z ∂μ, z.1 ≤ 0 ∧ pdist 0 z ≤ 1) (n : ℕ) :
    ∀ᵐ z ∂dyadicKernelMeasure μ T n, ‖z‖ ≤ max (T ^ 2) T := by
  filter_upwards [dyadicKernelMeasure_ae_past_radius μ hT hμ n] with z hz
  apply norm_le_of_pdist_zero_le hT
  exact hz.2.trans (by
    have hinv : 0 ≤ 1 / (2 : ℝ) ^ n := by positivity
    nlinarith [mul_nonneg hT hinv])

end GlobalPhi43.MW20
