/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.IntegratedKernelAffine
public import GlobalPhi43.Local.CompactCoefficientSource
public import GlobalPhi43.Local.PastAffineFiniteSum

/-! Quantitative affine bound for the finite fixed boundary-kernel family.
Only the original bounded field enters the source allowance. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory
open scoped ContDiff ENNReal

 theorem finite_boundary_kernel_affine_bound {I : Type*} [Fintype I]
    (k a : I → ParabolicSpace → ℝ)
    (hk : ∀ i, ContDiff ℝ ∞ (k i)) (hck : ∀ i, HasCompactSupport (k i))
    (ha : ∀ i, Continuous (a i)) (hca : ∀ i, HasCompactSupport (a i)) :
    ∃ C > 0, ∀ (μ : Measure ParabolicSpace), IsFiniteMeasure μ →
      ∀ (g : ParabolicSpace → ℝ) (H : ℝ), AEStronglyMeasurable g μ → 0 ≤ H →
      (∀ᵐ q ∂μ, |g q| ≤ H) → ∀ (x : ParabolicSpace) (R : ℝ), 0 ≤ R →
      pastAffineError (fun p => ∑ i, ∫ q, k i (p - q) * (a i q * g q) ∂μ) x R ≤
        ENNReal.ofReal (C * H * μ.real Set.univ * R ^ 2) := by
  classical
  choose S hS hkernel using fun i => exists_integrated_kernel_affine_bound (hk i) (hck i)
  choose A hA hsource using fun i => exists_compact_coefficient_source_bound (ha i) (hca i)
  have hw (i : I) : 0 ≤ 2 * S i * A i := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hS i)) (hA i)
  have hsum : 0 ≤ ∑ i, 2 * S i * A i := Finset.sum_nonneg fun i _ => hw i
  refine ⟨1 + ∑ i, 2 * S i * A i, by linarith, ?_⟩
  intro μ hμ g H hg hH hbound x R hR
  have : IsFiniteMeasure μ := hμ
  have hm : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
  have hi (i : I) := hsource i μ hμ g H hg hbound
  have hpoint (i : I) :
      2 * S i * (∫ q, |a i q * g q| ∂μ) * R ^ 2 ≤
        (2 * S i * A i) * H * μ.real Set.univ * R ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hi i).2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hS i))) (sq_nonneg R)
    nlinarith only [hh]
  have hterm (i : I) : 0 ≤ (2 * S i * A i) * H * μ.real Set.univ * R ^ 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw i) hH) hm) (sq_nonneg R)
  calc
    _ ≤ ∑ i, pastAffineError (fun p => ∫ q, k i (p - q) * (a i q * g q) ∂μ) x R :=
      pastAffineError_finset_sum_le Finset.univ _ x R
    _ ≤ ∑ i, ENNReal.ofReal (2 * S i * (∫ q, |a i q * g q| ∂μ) * R ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact hkernel i μ (fun q => a i q * g q) (hi i).1 x R hR
    _ ≤ ∑ i, ENNReal.ofReal ((2 * S i * A i) * H * μ.real Set.univ * R ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.ofReal_le_ofReal (hpoint i)
    _ = ENNReal.ofReal ((∑ i, 2 * S i * A i) * H * μ.real Set.univ * R ^ 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm i)]
      congr 1
      simp only [Finset.sum_mul]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hp : 0 ≤ H * μ.real Set.univ * R ^ 2 := mul_nonneg (mul_nonneg hH hm) (sq_nonneg R)
      nlinarith only [hp]

end GlobalPhi43.Local
