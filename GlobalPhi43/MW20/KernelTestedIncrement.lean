module

public import GlobalPhi43.MW20.KernelUniformDiagonal

/-!
# The tested increment in MW20 section 5.2.1

This is the actual double integral produced by the one-step kernel
factorisation. Exact max-distance support yields its power bound with
constant one, independently of the individual exponents. Integrability of
the outer tested increment follows from continuity and compact support.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set

/-- Parametric testing against a compactly concentrated finite measure is
continuous. For the infinite kernel, the required hypothesis is its closed-past support. -/
theorem continuous_integral_of_compact_ae (ν : Measure ParabolicSpace)
    [IsFiniteMeasure ν] (q : ℝ) (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ q)
    (G : ParabolicSpace × ParabolicSpace → ℝ) (hG : Continuous G) :
    Continuous (fun z => ∫ w, G (z, w) ∂ν) := by
  have hs : ν.restrict (Metric.closedBall 0 q) = ν := by
    apply Measure.restrict_eq_self_of_ae_mem
    simpa only [Metric.mem_closedBall, dist_zero_right] using hν
  have hc := continuous_parametric_integral_of_continuous (μ := ν)
    (f := fun z w => G (z, w)) hG (isCompact_closedBall (0 : ParabolicSpace) q)
  simpa only [hs] using hc

/-- The tested reconstruction increment with exact support and a finite
exponent set. This is an estimate of the literal germ difference integral. -/
theorem tested_increment_bound_of_past_support {ι : Type*} (A : Finset ι)
    (σ ν : Measure ParabolicSpace) [IsProbabilityMeasure σ] [IsFiniteMeasure ν]
    {r t q : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hσ : ∀ᵐ z ∂σ, z.1 ≤ 0 ∧ pdist 0 z ≤ r) (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ q)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) (x : ParabolicSpace)
    (B a b : ι → ℝ) (hB : ∀ i ∈ A, 0 ≤ B i) (ha : ∀ i ∈ A, 0 ≤ a i)
    (hcoh : ∀ z, z.1 ≤ 0 → pdist 0 z ≤ r →
      |∫ w, F (x, x + z + w) - F (x + z, x + z + w) ∂ν| ≤
        ∑ i ∈ A, B i * pdist 0 z ^ a i * t ^ b i) :
    Integrable (fun z => ∫ w, F (x, x + z + w) - F (x + z, x + z + w) ∂ν) σ ∧
      |∫ z, ∫ w, F (x, x + z + w) - F (x + z, x + z + w) ∂ν ∂σ| ≤
        ∑ i ∈ A, B i * r ^ a i * t ^ b i := by
  have hc : Continuous (fun p : ParabolicSpace × ParabolicSpace =>
      F (x, x + p.1 + p.2) - F (x + p.1, x + p.1 + p.2)) := by
    apply Continuous.sub <;> apply hF.comp <;> fun_prop
  have htest := continuous_integral_of_compact_ae ν q hν _ hc
  have his := integrable_of_continuous_compact_ae σ
    (Metric.closedBall 0 (max (r ^ 2) r)) (isCompact_closedBall _ _) (by
      filter_upwards [hσ] with z hz
      simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_of_pdist_zero_le hr hz.2)
    _ htest
  refine ⟨his, ?_⟩
  have hb := norm_integral_le_of_norm_le_const (μ := σ)
    (f := fun z => ∫ w, F (x, x + z + w) - F (x + z, x + z + w) ∂ν)
    (C := ∑ i ∈ A, B i * r ^ a i * t ^ b i) (by
      filter_upwards [hσ] with z hz
      rw [Real.norm_eq_abs]
      apply (hcoh z hz.1 hz.2).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (pdist_nonneg 0 z) hz.2 (ha i hi)) (hB i hi))
        (Real.rpow_nonneg ht _))
  simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hb

/-- At the factorisation step, inner and outer scales agree. The spatial and
testing exponents add exactly to the individual reconstruction exponents. -/
theorem reconstruction_increment_scale_identity {ι : Type*} (A : Finset ι)
    (B γ β : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    (∑ i ∈ A, B i * t ^ (γ i - β i) * t ^ β i) = ∑ i ∈ A, B i * t ^ γ i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, ← Real.rpow_add ht, sub_add_cancel]

end GlobalPhi43.MW20
