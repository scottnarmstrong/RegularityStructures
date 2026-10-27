module

public import GlobalPhi43.MW20.KernelProfile
public import GlobalPhi43.Local.RadiusGeometry

/-!
# Exact max-parabolic geometry of the MW20 factors
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- Exact scaling of the source max-parabolic distance from zero. -/
theorem pdist_zero_parabolicDilate {c : ℝ} (hc : 0 ≤ c) (z : ParabolicSpace) :
    Local.pdist 0 (parabolicDilate c z) = c * Local.pdist 0 z := by
  simp only [Local.pdist, parabolicDilate, Prod.fst_zero, Prod.snd_zero, zero_sub,
    abs_neg, norm_neg, abs_mul, abs_of_nonneg (sq_nonneg c), Real.sqrt_mul
      (sq_nonneg c), Real.sqrt_sq hc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  exact (mul_max_of_nonneg _ _ hc).symm

/-- The source past-unit support implies the exact closed-unit geometry. -/
theorem kernelProfileMeasure_ae_parabolic (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∀ᵐ z ∂kernelProfileMeasure Φ, z.1 ≤ 0 ∧ Local.pdist 0 z ≤ 1 := by
  unfold kernelProfileMeasure
  apply (ae_withDensity_iff (hΦ.smooth.continuous.measurable.ennreal_ofReal)).2
  apply ae_of_all
  intro z hz
  have hne : Φ z ≠ 0 := by intro he; simp [he] at hz
  have hs := hΦ.support (subset_tsupport Φ hne)
  refine ⟨hs.2.1.le, ?_⟩
  simp only [Local.pdist, Prod.fst_zero, Prod.snd_zero, zero_sub, abs_neg, norm_neg]
  apply max_le
  · apply (Real.sqrt_le_one).2
    rw [abs_le]
    exact ⟨hs.1.le, hs.2.1.le.trans (by norm_num)⟩
  · exact (norm_le_one_of_mem_kernelPastUnitBall hs).trans'
      (norm_snd_le z)

/-- Every actual pushed-forward factor has the exact past-looking support. -/
theorem dyadicKernelFactor_ae_parabolic (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ∀ᵐ z ∂dyadicKernelFactor (kernelProfileMeasure Φ) T n,
      z.1 ≤ 0 ∧ Local.pdist 0 z ≤ T / 2 ^ (n + 1) := by
  unfold dyadicKernelFactor
  apply (ae_map_iff (measurable_parabolicDilate _).aemeasurable
    (by
      apply MeasurableSet.inter
      · exact measurableSet_le measurable_fst measurable_const
      · exact measurableSet_le
          (show Measurable (fun x : ParabolicSpace => Local.pdist 0 x) by
            unfold Local.pdist; fun_prop) measurable_const)).2
  filter_upwards [kernelProfileMeasure_ae_parabolic Φ hΦ] with z hz
  have hc : 0 ≤ T / (2 : ℝ) ^ (n + 1) := by positivity
  refine ⟨mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hz.1, ?_⟩
  rw [pdist_zero_parabolicDilate hc]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2 hc

end GlobalPhi43.MW20
