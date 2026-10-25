/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiSq

/-!
# Products of single and pair integrals with general exponents

With `r = s(y - x)`, `r' = s(y' - x)`, `d = s(y - y')`:

* `i2Psi2LintBound_diag_prod_single`:
  `(∫ |A| s(y' - w)^(-e₁)) (∫ |A'| s(y - w')^(-e₂)) ≲ B² r^γ₁ r'^γ₂ (d^(-p₁) + r'^(-p₁))
  (d^(-p₂) + r^(-p₂))`, `pᵢ = γᵢ + eᵢ - 2 ∈ [0, 1]`;
* `i2Psi2LintBound_diag_prod_pair`: the same for
  `(∫ |A| s(y - w)^(-e₁) s(y' - w)^(-e₂)) (∫ |A'| s(y' - w')^(-e₃) s(y - w')^(-e₄))`,
  with `p₁ = γ₁ + e₁ + e₂ - 2`, `p₂ = γ₂ + e₃ + e₄ - 2`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Product of two single integrals**, general exponents. -/
theorem i2Psi2LintBound_diag_prod_single {γ₁ γ₂ e₁ e₂ : ℝ} (hγ₁0 : 0 ≤ γ₁) (hγ₁1 : γ₁ ≤ 1)
    (hγ₂0 : 0 ≤ γ₂) (hγ₂1 : γ₂ ≤ 1) (he₁5 : e₁ < 5) (he₂5 : e₂ < 5) (hγe₁ : 2 < γ₁ + e₁)
    (hγe₂ : 2 < γ₂ + e₂) (hp₁ : γ₁ + e₁ - 2 ≤ 1) (hp₂ : γ₂ + e₂ - 2 ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          (|i2Psi2Increment K x y q.1| * torusParabolicSize (y' - q.1) ^ (-e₁)) *
            (|i2Psi2Increment K x y' q.2| * torusParabolicSize (y - q.2) ^ (-e₂)))
          (C * B ^ 2 * torusParabolicSize (y - x) ^ γ₁ * torusParabolicSize (y' - x) ^ γ₂ *
            (torusParabolicSize (y - y') ^ (-(γ₁ + e₁ - 2)) +
              torusParabolicSize (y' - x) ^ (-(γ₁ + e₁ - 2))) *
            (torusParabolicSize (y - y') ^ (-(γ₂ + e₂ - 2)) +
              torusParabolicSize (y - x) ^ (-(γ₂ + e₂ - 2)))) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_kernel_sub_single hγ₁0 hγ₁1 he₁5 hγe₁
  obtain ⟨C2, hC2, h2⟩ := i2Psi2LintBound_kernel_sub_single hγ₂0 hγ₂1 he₂5 hγe₂
  refine ⟨4 * C1 * C2, by positivity, ?_⟩
  intro K B hK x y y' hr hr' hd
  obtain ⟨hB, hKm, -, -, -⟩ := id hK
  have mA := measurable_i2Psi2Increment hKm
  have hyx : 0 < torusParabolicSize (x - y) := torusParabolicSize_pos_of_sub_pos hr
  have hyx' : 0 < torusParabolicSize (x - y') := torusParabolicSize_pos_of_sub_pos hr'
  have hdd : 0 < torusParabolicSize (y' - y) := torusParabolicSize_pos_of_sub_pos hd
  have nr : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have f1 := h1 hK x y y' hd hyx'
  have f2 := h2 hK x y' y hdd hyx
  have hM1 : 0 ≤ C1 * B * torusParabolicSize (y - x) ^ γ₁ *
      (torusParabolicSize (y - y') ^ (-(γ₁ + e₁ - 2)) +
        torusParabolicSize (x - y') ^ (-(γ₁ + e₁ - 2))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1 hB) (nr _ _)) (add_nonneg (nr _ _) (nr _ _))
  have hprod := i2Psi2LintBound.prod_mul (μ := volume) (ν := volume)
    (((continuous_abs.measurable.comp (mA x y)).mul
      (measurable_torusParabolicSize_sub_rpow y' _)).aemeasurable)
    (((continuous_abs.measurable.comp (mA x y')).mul
      (measurable_torusParabolicSize_sub_rpow y _)).aemeasurable)
    (fun w => mul_nonneg (abs_nonneg _) (nr _ _)) hM1 f1 f2
  refine hprod.mono (fun q => le_rfl) ?_
  have t1 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y') (e := γ₁ + e₁ - 2)
    (by linarith) hp₁ hr'
  have t2 := torusParabolicSize_sub_rpow_neg_le (a := y') (b := y) (e := γ₂ + e₂ - 2)
    (by linarith) hp₂ hd
  have t3 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := γ₂ + e₂ - 2)
    (by linarith) hp₂ hr
  set D1 := torusParabolicSize (y - y') ^ (-(γ₁ + e₁ - 2))
  set R1 := torusParabolicSize (y' - x) ^ (-(γ₁ + e₁ - 2))
  set D2 := torusParabolicSize (y - y') ^ (-(γ₂ + e₂ - 2))
  set R2 := torusParabolicSize (y - x) ^ (-(γ₂ + e₂ - 2))
  have nD1 : 0 ≤ D1 := nr _ _
  have nR1 : 0 ≤ R1 := nr _ _
  have nD2 : 0 ≤ D2 := nr _ _
  have nR2 : 0 ≤ R2 := nr _ _
  have hA : C1 * B * torusParabolicSize (y - x) ^ γ₁ *
      (D1 + torusParabolicSize (x - y') ^ (-(γ₁ + e₁ - 2))) ≤
      C1 * B * torusParabolicSize (y - x) ^ γ₁ * (2 * (D1 + R1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hC1 hB) (nr _ _))
  have hN : C2 * B * torusParabolicSize (y' - x) ^ γ₂ *
      (torusParabolicSize (y' - y) ^ (-(γ₂ + e₂ - 2)) +
        torusParabolicSize (x - y) ^ (-(γ₂ + e₂ - 2))) ≤
      C2 * B * torusParabolicSize (y' - x) ^ γ₂ * (2 * (D2 + R2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hC2 hB) (nr _ _))
  have hN0 : 0 ≤ C2 * B * torusParabolicSize (y' - x) ^ γ₂ *
      (torusParabolicSize (y' - y) ^ (-(γ₂ + e₂ - 2)) +
        torusParabolicSize (x - y) ^ (-(γ₂ + e₂ - 2))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC2 hB) (nr _ _)) (add_nonneg (nr _ _) (nr _ _))
  have hA0 : 0 ≤ C1 * B * torusParabolicSize (y - x) ^ γ₁ * (2 * (D1 + R1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1 hB) (nr _ _)) (by positivity)
  calc _ ≤ (C1 * B * torusParabolicSize (y - x) ^ γ₁ * (2 * (D1 + R1))) *
        (C2 * B * torusParabolicSize (y' - x) ^ γ₂ * (2 * (D2 + R2))) :=
        mul_le_mul hA hN hN0 hA0
    _ = _ := by ring

/-- **Product of two pair integrals**, general exponents. -/
theorem i2Psi2LintBound_diag_prod_pair {γ₁ γ₂ e₁ e₂ e₃ e₄ : ℝ} (hγ₁0 : 0 ≤ γ₁) (hγ₁1 : γ₁ ≤ 1)
    (hγ₂0 : 0 ≤ γ₂) (hγ₂1 : γ₂ ≤ 1) (he₁ : 0 ≤ e₁) (he₂ : 0 < e₂) (h5₁ : 3 + γ₁ + e₁ < 5)
    (he₂5 : e₂ < 5) (hs₁ : 2 < γ₁ + e₁ + e₂) (he₃ : 0 ≤ e₃) (he₄ : 0 < e₄)
    (h5₃ : 3 + γ₂ + e₃ < 5) (he₄5 : e₄ < 5) (hs₂ : 2 < γ₂ + e₃ + e₄)
    (hp₁ : γ₁ + e₁ + e₂ - 2 ≤ 1) (hp₂ : γ₂ + e₃ + e₄ - 2 ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          (|i2Psi2Increment K x y q.1| * (torusParabolicSize (y - q.1) ^ (-e₁) *
              torusParabolicSize (y' - q.1) ^ (-e₂))) *
            (|i2Psi2Increment K x y' q.2| * (torusParabolicSize (y' - q.2) ^ (-e₃) *
              torusParabolicSize (y - q.2) ^ (-e₄))))
          (C * B ^ 2 * torusParabolicSize (y - x) ^ γ₁ * torusParabolicSize (y' - x) ^ γ₂ *
            (torusParabolicSize (y - y') ^ (-(γ₁ + e₁ + e₂ - 2)) +
              torusParabolicSize (y' - x) ^ (-(γ₁ + e₁ + e₂ - 2))) *
            (torusParabolicSize (y - y') ^ (-(γ₂ + e₃ + e₄ - 2)) +
              torusParabolicSize (y - x) ^ (-(γ₂ + e₃ + e₄ - 2)))) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_kernel_sub_pair hγ₁0 hγ₁1 he₁ he₂ h5₁ he₂5 hs₁
  obtain ⟨C2, hC2, h2⟩ := i2Psi2LintBound_kernel_sub_pair hγ₂0 hγ₂1 he₃ he₄ h5₃ he₄5 hs₂
  refine ⟨18 * C1 * C2, by positivity, ?_⟩
  intro K B hK x y y' hr hr' hd
  obtain ⟨hB, hKm, -, -, -⟩ := id hK
  have mA := measurable_i2Psi2Increment hKm
  have hyx : 0 < torusParabolicSize (x - y) := torusParabolicSize_pos_of_sub_pos hr
  have hyx' : 0 < torusParabolicSize (x - y') := torusParabolicSize_pos_of_sub_pos hr'
  have hdd : 0 < torusParabolicSize (y' - y) := torusParabolicSize_pos_of_sub_pos hd
  have nr : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have f1 := h1 hK x y y y' hd hyx' hd
  have f2 := h2 hK x y' y' y hdd hyx hdd
  have hM1 : 0 ≤ C1 * B * torusParabolicSize (y - x) ^ γ₁ *
      (torusParabolicSize (y - y') ^ (-(γ₁ + e₁ + e₂ - 2)) +
        torusParabolicSize (x - y') ^ (-(γ₁ + e₁ + e₂ - 2)) +
        2 * torusParabolicSize (y - y') ^ (-(γ₁ + e₁ + e₂ - 2))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1 hB) (nr _ _))
      (add_nonneg (add_nonneg (nr _ _) (nr _ _)) (mul_nonneg (by norm_num) (nr _ _)))
  have hprod := i2Psi2LintBound.prod_mul (μ := volume) (ν := volume)
    (((continuous_abs.measurable.comp (mA x y)).mul
      ((measurable_torusParabolicSize_sub_rpow y _).mul
        (measurable_torusParabolicSize_sub_rpow y' _))).aemeasurable)
    (((continuous_abs.measurable.comp (mA x y')).mul
      ((measurable_torusParabolicSize_sub_rpow y' _).mul
        (measurable_torusParabolicSize_sub_rpow y _))).aemeasurable)
    (fun w => mul_nonneg (abs_nonneg _) (mul_nonneg (nr _ _) (nr _ _))) hM1 f1 f2
  refine hprod.mono (fun q => le_rfl) ?_
  have t1 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y') (e := γ₁ + e₁ + e₂ - 2)
    (by linarith) hp₁ hr'
  have t3 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := γ₂ + e₃ + e₄ - 2)
    (by linarith) hp₂ hr
  have t2 := torusParabolicSize_sub_rpow_neg_le (a := y') (b := y) (e := γ₂ + e₃ + e₄ - 2)
    (by linarith) hp₂ hd
  set D1 := torusParabolicSize (y - y') ^ (-(γ₁ + e₁ + e₂ - 2))
  set R1 := torusParabolicSize (y' - x) ^ (-(γ₁ + e₁ + e₂ - 2))
  set D2 := torusParabolicSize (y - y') ^ (-(γ₂ + e₃ + e₄ - 2))
  set R2 := torusParabolicSize (y - x) ^ (-(γ₂ + e₃ + e₄ - 2))
  have nD1 : 0 ≤ D1 := nr _ _
  have nR1 : 0 ≤ R1 := nr _ _
  have nD2 : 0 ≤ D2 := nr _ _
  have nR2 : 0 ≤ R2 := nr _ _
  have hA : C1 * B * torusParabolicSize (y - x) ^ γ₁ *
      (D1 + torusParabolicSize (x - y') ^ (-(γ₁ + e₁ + e₂ - 2)) + 2 * D1) ≤
      C1 * B * torusParabolicSize (y - x) ^ γ₁ * (3 * (D1 + R1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hC1 hB) (nr _ _))
  have hN : C2 * B * torusParabolicSize (y' - x) ^ γ₂ *
      (torusParabolicSize (y' - y) ^ (-(γ₂ + e₃ + e₄ - 2)) +
        torusParabolicSize (x - y) ^ (-(γ₂ + e₃ + e₄ - 2)) +
        2 * torusParabolicSize (y' - y) ^ (-(γ₂ + e₃ + e₄ - 2))) ≤
      C2 * B * torusParabolicSize (y' - x) ^ γ₂ * (6 * (D2 + R2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hC2 hB) (nr _ _))
  have hN0 : 0 ≤ C2 * B * torusParabolicSize (y' - x) ^ γ₂ *
      (torusParabolicSize (y' - y) ^ (-(γ₂ + e₃ + e₄ - 2)) +
        torusParabolicSize (x - y) ^ (-(γ₂ + e₃ + e₄ - 2)) +
        2 * torusParabolicSize (y' - y) ^ (-(γ₂ + e₃ + e₄ - 2))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC2 hB) (nr _ _))
      (add_nonneg (add_nonneg (nr _ _) (nr _ _)) (mul_nonneg (by norm_num) (nr _ _)))
  have hA0 : 0 ≤ C1 * B * torusParabolicSize (y - x) ^ γ₁ * (3 * (D1 + R1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1 hB) (nr _ _)) (by positivity)
  calc _ ≤ (C1 * B * torusParabolicSize (y - x) ^ γ₁ * (3 * (D1 + R1))) *
        (C2 * B * torusParabolicSize (y' - x) ^ γ₂ * (6 * (D2 + R2))) :=
        mul_le_mul hA hN hN0 hA0
    _ = _ := by ring

end RegularityStructures

end
