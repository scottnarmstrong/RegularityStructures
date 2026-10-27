/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SmoothingComparison

/-! The finite A_+ powers in the smoothing comparison. Both exponent
inequalities are retained; negative beta would not justify replacing d(x,y)
by the larger base-point radius R. -/
public section

namespace GlobalPhi43.Local

open MeasureTheory RegularityStructures
open scoped BigOperators

/-- Dominate the three-point powers on the two legal radius ranges. -/
theorem three_point_power_sum_le {I : Type*} (s : Finset I) (β : I → ℝ)
    {γ R T : ℝ} (x y z : ParabolicSpace)
    (hβ : ∀ i ∈ s, 0 ≤ β i) (hβγ : ∀ i ∈ s, β i ≤ γ)
    (hxy : pdist x y ≤ R) (hyz : pdist y z ≤ T) :
    (∑ i ∈ s, pdist x y ^ β i * pdist y z ^ (γ - β i)) ≤
      ∑ i ∈ s, R ^ β i * T ^ (γ - β i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul
    (Real.rpow_le_rpow (pdist_nonneg x y) hxy (hβ i hi))
    (Real.rpow_le_rpow (pdist_nonneg y z) hyz (sub_nonneg.mpr (hβγ i hi)))
    (Real.rpow_nonneg (pdist_nonneg y z) _)
    (Real.rpow_nonneg ((pdist_nonneg x y).trans hxy) _)

/-- The complete finite-power averaging estimate at a base point y.
The remaining kernel and seminorm attachments are explicit in its hypotheses;
no smoothing-comparison inequality is assumed. -/
theorem recentered_smoothing_comparison_powers {I : Type*} (s : Finset I) (β : I → ℝ)
    (μ : Measure ParabolicSpace) [IsProbabilityMeasure μ]
    (U : ParabolicSpace → ParabolicSpace → ℝ) (x y : ParabolicSpace)
    (ν : Fin 3 → ℝ) {γ R T M K : ℝ} (hγ : 0 ≤ γ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hβ : ∀ i ∈ s, 0 ≤ β i) (hβγ : ∀ i ∈ s, β i ≤ γ)
    (hxy : pdist x y ≤ R)
    (hf : Integrable (fun w => U x (y + w)) μ)
    (hcoord : ∀ i, Integrable (fun w : ParabolicSpace => w.2 i) μ)
    (hzero : ∀ i, ∫ w : ParabolicSpace, w.2 i ∂μ = 0)
    (hsupp : ∀ᵐ w ∂μ, pdist 0 w ≤ T)
    (hthree : ∀ᵐ w ∂μ, |U x (y + w) - U x y - U y (y + w)| ≤
      M * ∑ i ∈ s, pdist x y ^ β i * pdist y (y + w) ^ (γ - β i))
    (hrem : ∀ᵐ w ∂μ, |U y (y + w) - spatialLinear ν w| ≤
      K * pdist y (y + w) ^ γ) :
    |(∫ w, U x (y + w) ∂μ) - U x y| ≤
      M * (∑ i ∈ s, R ^ β i * T ^ (γ - β i)) + K * T ^ γ := by
  apply recentered_smoothing_comparison μ U x y ν hγ hK hf hcoord hzero hsupp
    _ hrem
  filter_upwards [hsupp, hthree] with w hw hwt
  apply hwt.trans
  apply mul_le_mul_of_nonneg_left _ hM
  apply three_point_power_sum_le s β x y (y + w) hβ hβγ hxy
  simpa only [pdist_add_right] using hw

end GlobalPhi43.Local
