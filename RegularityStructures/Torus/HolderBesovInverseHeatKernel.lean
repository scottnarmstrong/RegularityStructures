/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovCutoffKernel

/-!
# Uniform kernels for the dyadic inverse-heat multiplier

At time `s = 2^(-2n)`, the inverse heat multiplier is a fixed smooth profile in frequency
coordinates `k/2^n`. Localising to the actual LP block gives a uniform L1 bound. The two consecutive
cutoffs use the fixed profiles with parameters `1` and `1/4`. This is the inverse-multiplier step in
the comparison of the LP norm with the heat norm (2.3) of the statement.
-/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus
open scoped ENNReal SchwartzMap

namespace RegularityStructures

/-- The inverse heat character at time `2^(-2n)`, factored by coordinate. -/
def torusInverseHeatWeight (n : ℕ) (k : Fin 3 → ℤ) : ℂ :=
  ∏ i : Fin 3, Complex.exp ((4 * Real.pi ^ 2 *
    (((2 : ℝ) ^ n)⁻¹ * (k i : ℝ)) ^ 2 : ℝ) : ℂ)

/-- The literal dyadic symbol multiplied by the inverse heat character. -/
def torusDyadicInverseHeatKernel (n : ℕ) : C(Torus3, ℂ) :=
  ∑ k ∈ torusLPFrequencyBox n,
    ((torusDyadicFrequencySymbol n k : ℂ) * torusInverseHeatWeight n k) • mFourier k

private def innerInverseHeatProfile : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ 2 (by norm_num)).toContinuousLinearEquiv
      (torusLPInverseHeatProfile (1 / 4))

private theorem innerInverseHeatProfile_apply (u : ℝ) :
    innerInverseHeatProfile u = (torusLPBump (2 * u) : ℂ) *
      Complex.exp ((4 * Real.pi ^ 2 * u ^ 2 : ℝ) : ℂ) := by
  change torusLPInverseHeatProfile (1 / 4) (2 * u) = _
  rw [torusLPInverseHeatProfile_apply]
  congr 2
  congr 1
  ring

private theorem innerInverseHeatProfile_eq_zero {u : ℝ} (hu : 2 ≤ |u|) :
    innerInverseHeatProfile u = 0 := by
  change torusLPInverseHeatProfile (1 / 4) (2 * u) = 0
  apply torusLPInverseHeatProfile_eq_zero
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [hu]

private theorem inverseProfile_prod (n : ℕ) (k : Fin 3 → ℤ) :
    (∏ i : Fin 3, torusLPInverseHeatProfile 1 ((k i : ℝ) / (2 : ℝ) ^ n)) =
      (torusLowFrequencySymbol n k : ℂ) * torusInverseHeatWeight n k := by
  simp only [torusLPInverseHeatProfile_apply, mul_one, Finset.prod_mul_distrib,
    torusLowFrequencySymbol, Complex.ofReal_prod, torusInverseHeatWeight,
    div_eq_mul_inv]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;> rw [mul_comm (k i : ℝ)]

private theorem innerProfile_prod (n : ℕ) (k : Fin 3 → ℤ) :
    (∏ i : Fin 3, innerInverseHeatProfile ((k i : ℝ) / (2 : ℝ) ^ (n + 1))) =
      (torusLowFrequencySymbol n k : ℂ) * torusInverseHeatWeight (n + 1) k := by
  simp only [innerInverseHeatProfile_apply, Finset.prod_mul_distrib,
    torusLowFrequencySymbol, Complex.ofReal_prod, torusInverseHeatWeight]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    congr 1
    rw [pow_succ]
    field_simp
  · apply Finset.prod_congr rfl
    intro i _
    rw [div_eq_mul_inv, mul_comm (k i : ℝ)]

private theorem inverseKernel_zero :
    torusDyadicInverseHeatKernel 0 =
      torusTensorFiniteKernel (fun _ : Fin 3 => torusLPInverseHeatProfile 1) 0 := by
  ext x
  simp only [torusDyadicInverseHeatKernel, torusTensorFiniteKernel, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, torusDyadicFrequencySymbol_zero, inverseProfile_prod]

private theorem inverseKernel_succ (n : ℕ) :
    torusDyadicInverseHeatKernel (n + 1) =
      torusTensorFiniteKernel (fun _ : Fin 3 => torusLPInverseHeatProfile 1) (n + 1) -
        torusTensorFiniteKernel (fun _ : Fin 3 => innerInverseHeatProfile) (n + 1) := by
  ext x
  simp only [torusDyadicInverseHeatKernel, torusTensorFiniteKernel, ContinuousMap.sum_apply,
    ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul, inverseProfile_prod,
    innerProfile_prod, torusDyadicFrequencySymbol_succ, Complex.ofReal_sub,
    sub_mul, Finset.sum_sub_distrib]

theorem lintegral_torusDyadicInverseHeatKernel_bound_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫⁻ x : Torus3, ‖torusDyadicInverseHeatKernel n x‖ₑ) ≤ ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := torusTensorFiniteKernel_bound_uniform
    (fun _ : Fin 3 => torusLPInverseHeatProfile 1)
    (fun _ _ hu => torusLPInverseHeatProfile_eq_zero 1 hu)
  obtain ⟨C₁, hC₁, hb₁⟩ := torusTensorFiniteKernel_bound_uniform
    (fun _ : Fin 3 => innerInverseHeatProfile)
    (fun _ _ hu => innerInverseHeatProfile_eq_zero hu)
  refine ⟨C₀ + C₁, add_nonneg hC₀ hC₁, fun n => ?_⟩
  rw [ENNReal.ofReal_add hC₀ hC₁]
  cases n with
  | zero =>
    rw [inverseKernel_zero]
    exact (hb₀ 0).trans (le_add_of_nonneg_right zero_le)
  | succ n =>
    rw [inverseKernel_succ]
    calc
      _ ≤ ∫⁻ x : Torus3,
          ‖torusTensorFiniteKernel (fun _ : Fin 3 => torusLPInverseHeatProfile 1) (n + 1) x‖ₑ +
          ‖torusTensorFiniteKernel (fun _ : Fin 3 => innerInverseHeatProfile) (n + 1) x‖ₑ := by
        apply lintegral_mono
        intro x
        exact enorm_sub_le
      _ = _ := lintegral_add_left
        (torusTensorFiniteKernel (fun _ : Fin 3 => torusLPInverseHeatProfile 1)
          (n + 1)).continuous.enorm.measurable _
      _ ≤ _ := add_le_add (hb₀ (n + 1)) (hb₁ (n + 1))

end RegularityStructures

end
