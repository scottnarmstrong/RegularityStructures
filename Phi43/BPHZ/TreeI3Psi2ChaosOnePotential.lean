/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneSplit
public import Phi43.BPHZ.TreeI3PsiLeaves

/-!
# Convolution estimates for the absolute value of the kernel `J`

* `integral_swap_nonneg`: Tonelli for nonnegative functions in terms of Bochner integrals;
* `abs_J_mul_J_le`: `∫ |J(w - y)| |J(w' - y)| dy ≤ C B² s(w - w')^(-1)`;
* `power_mul_abs_J_le`: `∫ s(c - y)^(-a) |J(w - y)| dy ≤ C B s(c - w)^(2-a)` for `a ∈ (2, 5)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- Tonelli for nonnegative functions: finiteness of one iterated integral gives integrability on
the product and equality of the iterated integrals. -/
theorem integral_swap_nonneg {G : SpaceTime → SpaceTime → ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry G) (volume.prod volume))
    (h0 : ∀ w y, 0 ≤ G w y) (hG : ∀ᵐ w : SpaceTime ∂volume, Integrable (G w))
    (hH : Integrable (fun w => ∫ y, G w y)) :
    Integrable (Function.uncurry G) (volume.prod volume) ∧
      Integrable (fun y => ∫ w, G w y) ∧ ∫ y, ∫ w, G w y = ∫ w, ∫ y, G w y := by
  have hint : Integrable (Function.uncurry G) (volume.prod volume) := by
    refine (integrable_prod_iff hm).2 ⟨hG, ?_⟩
    refine hH.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (h0 _ _)]
  exact ⟨hint, hint.integral_prod_right, (integral_integral_swap hint).symm⟩

theorem abs_J_le_singularPow {J : SpaceTime → ℝ} {B : ℝ}
    (hJ : ∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    {w y : SpaceTime} (h : 0 < torusParabolicSize (w - y)) :
    |J (w - y)| ≤ B * singularPow 3 w y := hJ _ h

/-- `∫ |J(w - y)| |J(w' - y)| dy ≤ C B² s(w - w')^(-1)`. -/
theorem abs_J_mul_J_le {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J : SpaceTime → ℝ}, Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      ∀ w w' : SpaceTime, 0 < torusParabolicSize (w - w') →
        Integrable (fun y => |J (w - y)| * |J (w' - y)|) ∧
          ∫ y, |J (w - y)| * |J (w' - y)| ≤ C * B ^ 2 * torusParabolicSize (w - w') ^ (5 - 3 - 3 : ℝ) := by
  obtain ⟨C, hC, h⟩ := integrable_and_integral_singularPow_mul_le (a := 3) (b := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun {J} hJm hJ w w' hww => ?_⟩
  obtain ⟨i, b⟩ := h w w' hww
  have hmaj : Integrable (fun y => B ^ 2 * (singularPow 3 w y * singularPow 3 w' y)) :=
    i.const_mul _
  have hm : Measurable (fun y => |J (w - y)| * |J (w' - y)|) :=
    (continuous_abs.measurable.comp (hJm.comp (measurable_const.sub measurable_id))).mul
      (continuous_abs.measurable.comp (hJm.comp (measurable_const.sub measurable_id)))
  have hle : ∀ᵐ y : SpaceTime ∂volume, |J (w - y)| * |J (w' - y)| ≤
      B ^ 2 * (singularPow 3 w y * singularPow 3 w' y) := by
    filter_upwards [ae_torusParabolicSize_sub_pos w, ae_torusParabolicSize_sub_pos w'] with y a b
    have := mul_le_mul (abs_J_le_singularPow hJ a) (abs_J_le_singularPow hJ b) (abs_nonneg _)
      (mul_nonneg hB (singularPow_nonneg _ _ _))
    refine this.trans (le_of_eq ?_)
    ring
  refine ⟨Integrable.mono' hmaj hm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hle] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hy
  · calc ∫ y, |J (w - y)| * |J (w' - y)| ≤ ∫ y, B ^ 2 * (singularPow 3 w y * singularPow 3 w' y) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)) hmaj hle
      _ = B ^ 2 * ∫ y, singularPow 3 w y * singularPow 3 w' y := by rw [integral_const_mul]
      _ ≤ B ^ 2 * (C * torusParabolicSize (w - w') ^ (5 - 3 - 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left b (sq_nonneg B)
      _ = _ := by ring

/-- `∫ s(c - y)^(-a) |J(w - y)| dy ≤ C B s(c - w)^(5-a-3)`. -/
theorem power_mul_abs_J_le {a B : ℝ} (hB : 0 ≤ B) (ha : 0 < a) (ha5 : a < 5) (hab : 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J : SpaceTime → ℝ}, Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      ∀ c w : SpaceTime, 0 < torusParabolicSize (c - w) →
        Integrable (fun y => singularPow a c y * |J (w - y)|) ∧
          ∫ y, singularPow a c y * |J (w - y)| ≤ C * B * torusParabolicSize (c - w) ^ (5 - a - 3) := by
  obtain ⟨C, hC, h⟩ := integrable_and_integral_singularPow_mul_le (a := a) (b := 3)
    ha ha5 (by norm_num) (by norm_num) (by linarith)
  refine ⟨C, hC, fun {J} hJm hJ c w hcw => ?_⟩
  obtain ⟨i, b⟩ := h c w hcw
  have hmaj : Integrable (fun y => B * (singularPow a c y * singularPow 3 w y)) := i.const_mul _
  have hm : Measurable (fun y => singularPow a c y * |J (w - y)|) :=
    (measurable_singularPow a c).mul
      (continuous_abs.measurable.comp (hJm.comp (measurable_const.sub measurable_id)))
  have hle : ∀ᵐ y : SpaceTime ∂volume, singularPow a c y * |J (w - y)| ≤
      B * (singularPow a c y * singularPow 3 w y) := by
    filter_upwards [ae_torusParabolicSize_sub_pos w] with y a'
    have := mul_le_mul_of_nonneg_left (abs_J_le_singularPow hJ a') (singularPow_nonneg a c y)
    refine this.trans (le_of_eq ?_)
    ring
  refine ⟨Integrable.mono' hmaj hm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hle] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (singularPow_nonneg _ _ _) (abs_nonneg _))]
    exact hy
  · calc ∫ y, singularPow a c y * |J (w - y)| ≤ ∫ y, B * (singularPow a c y * singularPow 3 w y) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
            mul_nonneg (singularPow_nonneg _ _ _) (abs_nonneg _)) hmaj hle
      _ = B * ∫ y, singularPow a c y * singularPow 3 w y := by rw [integral_const_mul]
      _ ≤ B * (C * torusParabolicSize (c - w) ^ (5 - a - 3)) :=
          mul_le_mul_of_nonneg_left b hB
      _ = _ := by ring

end RegularityStructures

end
