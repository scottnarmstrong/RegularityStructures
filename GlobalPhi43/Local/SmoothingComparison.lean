/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.DefectSmoothing

/-! The integral step of the Schauder smoothing comparison.
The affine remainder is controlled on the actual tested pairs (y,y+w).
Attachment to the limiting MW20 kernel and its seminorms remains separate. -/
public noncomputable section

namespace GlobalPhi43.Local

open MeasureTheory RegularityStructures
open scoped BigOperators

/-- A spatial affine increment has no time component. -/
@[expose] def spatialLinear (ν : Fin 3 → ℝ) (w : ParabolicSpace) : ℝ :=
  ∑ i, ν i * w.2 i

/-- Coordinate integrability suffices for every fixed spatial coefficient. -/
theorem spatialLinear_integrable (μ : Measure ParabolicSpace) (ν : Fin 3 → ℝ)
    (hcoord : ∀ i, Integrable (fun w : ParabolicSpace => w.2 i) μ) :
    Integrable (spatialLinear ν) μ := by
  exact integrable_finsetSum _ fun i _ => (hcoord i).const_mul (ν i)

/-- Spatial first moments cancel the entire affine increment. -/
theorem integral_spatialLinear_eq_zero (μ : Measure ParabolicSpace) (ν : Fin 3 → ℝ)
    (hcoord : ∀ i, Integrable (fun w : ParabolicSpace => w.2 i) μ)
    (hzero : ∀ i, ∫ w : ParabolicSpace, w.2 i ∂μ = 0) :
    ∫ w, spatialLinear ν w ∂μ = 0 := by
  unfold spatialLinear
  rw [integral_finsetSum Finset.univ (fun i _ => (hcoord i).const_mul (ν i))]
  simp only [integral_const_mul, hzero, mul_zero, Finset.sum_const_zero]

/-- The abstract averaging calculation: insert the recentered section, subtract
its affine increment, and cancel that increment under the integral. -/
theorem average_comparison_of_remainders {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f g a : E → ℝ)
    {k C₁ C₂ : ℝ} (hf : Integrable f μ) (ha : Integrable a μ)
    (hmoment : ∫ w, a w ∂μ = 0)
    (hthree : ∀ᵐ w ∂μ, |f w - k - g w| ≤ C₁)
    (hrem : ∀ᵐ w ∂μ, |g w - a w| ≤ C₂) :
    |(∫ w, f w ∂μ) - k| ≤ C₁ + C₂ := by
  have hbound : ∀ᵐ w ∂μ, ‖f w - k - a w‖ ≤ C₁ + C₂ := by
    filter_upwards [hthree, hrem] with w hw₁ hw₂
    rw [Real.norm_eq_abs]
    calc
      _ = |(f w - k - g w) + (g w - a w)| := by congr 1; ring
      _ ≤ |f w - k - g w| + |g w - a w| := abs_add_le _ _
      _ ≤ _ := add_le_add hw₁ hw₂
  have heq : (∫ w, f w - k - a w ∂μ) = (∫ w, f w ∂μ) - k := by
    rw [integral_sub (hf.sub' (integrable_const k)) ha,
      integral_sub hf (integrable_const k), integral_const, hmoment]
    simp
  have hnorm := norm_integral_le_of_norm_le_const hbound
  rw [heq] at hnorm
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hnorm

/-- Relative kernel variables preserve the parabolic distance in the
past-looking smoothing convention. -/
theorem pdist_add_right (y w : ParabolicSpace) : pdist y (y + w) = pdist 0 w := by
  have ht : y.1 - (y.1 + w.1) = -w.1 := by ring
  have hx : y.2 - (y.2 + w.2) = -w.2 := by abel
  change max (Real.sqrt |y.1 - (y.1 + w.1)|) ‖y.2 - (y.2 + w.2)‖ =
    max (Real.sqrt |0 - w.1|) ‖0 - w.2‖
  rw [ht, hx]
  simp only [zero_sub]

/-- The pointwise smoothing comparison for a two-variable expansion.
No time reflection is used: the sampled point is y+w. -/
theorem recentered_smoothing_comparison (μ : Measure ParabolicSpace)
    [IsProbabilityMeasure μ] (U : ParabolicSpace → ParabolicSpace → ℝ)
    (x y : ParabolicSpace) (ν : Fin 3 → ℝ) {γ T K₁ K₂ : ℝ}
    (hγ : 0 ≤ γ) (hK₂ : 0 ≤ K₂)
    (hf : Integrable (fun w => U x (y + w)) μ)
    (hcoord : ∀ i, Integrable (fun w : ParabolicSpace => w.2 i) μ)
    (hzero : ∀ i, ∫ w : ParabolicSpace, w.2 i ∂μ = 0)
    (hsupp : ∀ᵐ w ∂μ, pdist 0 w ≤ T)
    (hthree : ∀ᵐ w ∂μ, |U x (y + w) - U x y - U y (y + w)| ≤ K₁)
    (hrem : ∀ᵐ w ∂μ, |U y (y + w) - spatialLinear ν w| ≤
      K₂ * pdist y (y + w) ^ γ) :
    |(∫ w, U x (y + w) ∂μ) - U x y| ≤ K₁ + K₂ * T ^ γ := by
  apply average_comparison_of_remainders μ (fun w => U x (y + w))
    (fun w => U y (y + w)) (spatialLinear ν) hf
    (spatialLinear_integrable μ ν hcoord) (integral_spatialLinear_eq_zero μ ν hcoord hzero)
    hthree
  filter_upwards [hsupp, hrem] with w hw hwr
  apply hwr.trans
  apply mul_le_mul_of_nonneg_left _ hK₂
  rw [pdist_add_right]
  exact Real.rpow_le_rpow (pdist_nonneg 0 w) hw hγ

end GlobalPhi43.Local
