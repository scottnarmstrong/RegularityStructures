/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsCovariance
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Young's inequality `L^{3/2} * L^{3/2} → L³` on `ℝ × T³`

For measurable `u, v` the correlation `Θ(z) = ∫⁻ ‖u(z + w)‖ₑ ‖v(w)‖ₑ dw` satisfies
`∫⁻ Θ³ ≤ (‖u‖_{3/2}^{3/2} ‖v‖_{3/2}^{3/2})²`.  The proof is the three-factor Hölder inequality
for `((ab)^{1/2}, a^{1/2}, b^{1/2})` followed by Tonelli and translation invariance.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem constantsRate_lintegral_mul_three_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {a b c : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (hc : AEMeasurable c μ) :
    ∫⁻ x, a x * b x * c x ∂μ ≤
      (∫⁻ x, a x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) * (∫⁻ x, b x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) *
        (∫⁻ x, c x ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) := by
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 3))
    (f := ![fun x => a x ^ (3 : ℝ), fun x => b x ^ (3 : ℝ), fun x => c x ^ (3 : ℝ)])
    (p := fun _ => (1 / 3 : ℝ)) (by
      intro i _
      fin_cases i
      · exact ha.pow_const _
      · exact hb.pow_const _
      · exact hc.pow_const _)
    (by simp [Finset.sum_const]) (by intros; norm_num)
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  have e : ∀ y : ℝ≥0∞, (y ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = y := by
    intro y
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [e] at h
  exact h

/-- The pointwise cubic bound `(∫ a b)³ ≤ (∫ a^{3/2} b^{3/2}) (∫ a^{3/2}) (∫ b^{3/2})`. -/
theorem constantsRate_lintegral_cube_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ x, a x * b x ∂μ) ^ (3 : ℝ) ≤
      (∫⁻ x, a x ^ (3 / 2 : ℝ) * b x ^ (3 / 2 : ℝ) ∂μ) * (∫⁻ x, a x ^ (3 / 2 : ℝ) ∂μ) *
        ∫⁻ x, b x ^ (3 / 2 : ℝ) ∂μ := by
  have h := constantsRate_lintegral_mul_three_le μ
    (a := fun x => (a x * b x) ^ (1 / 2 : ℝ)) (b := fun x => a x ^ (1 / 2 : ℝ))
    (c := fun x => b x ^ (1 / 2 : ℝ)) ((ha.mul hb).pow_const _) (ha.pow_const _) (hb.pow_const _)
  have e1 : ∀ x, (a x * b x) ^ (1 / 2 : ℝ) * a x ^ (1 / 2 : ℝ) * b x ^ (1 / 2 : ℝ) =
      a x * b x := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have : a x ^ (1 / 2 : ℝ) * a x ^ (1 / 2 : ℝ) = a x := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have h2 : b x ^ (1 / 2 : ℝ) * b x ^ (1 / 2 : ℝ) = b x := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    calc
      a x ^ (1 / 2 : ℝ) * b x ^ (1 / 2 : ℝ) * a x ^ (1 / 2 : ℝ) * b x ^ (1 / 2 : ℝ) =
          (a x ^ (1 / 2 : ℝ) * a x ^ (1 / 2 : ℝ)) * (b x ^ (1 / 2 : ℝ) * b x ^ (1 / 2 : ℝ)) := by
        ring
      _ = a x * b x := by rw [this, h2]
  have e2 : ∀ x, ((a x * b x) ^ (1 / 2 : ℝ)) ^ (3 : ℝ) = a x ^ (3 / 2 : ℝ) * b x ^ (3 / 2 : ℝ) := by
    intro x
    rw [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2 * 3)]
    norm_num
  have e3 : ∀ y : ℝ≥0∞, (y ^ (1 / 2 : ℝ)) ^ (3 : ℝ) = y ^ (3 / 2 : ℝ) := by
    intro y
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [e1, e2, e3] at h
  calc
    (∫⁻ x, a x * b x ∂μ) ^ (3 : ℝ) ≤
        ((∫⁻ x, a x ^ (3 / 2 : ℝ) * b x ^ (3 / 2 : ℝ) ∂μ) ^ (1 / 3 : ℝ) *
          (∫⁻ x, a x ^ (3 / 2 : ℝ) ∂μ) ^ (1 / 3 : ℝ) *
          (∫⁻ x, b x ^ (3 / 2 : ℝ) ∂μ) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
      simp only [← ENNReal.rpow_mul]
      norm_num

theorem constantsRate_young_lintegral {u v : SpaceTime → ℝ} (hu : Measurable u)
    (hv : Measurable v) (hFu : ∫⁻ z, ‖u z‖ₑ ^ (3 / 2 : ℝ) ≠ ⊤)
    (hFv : ∫⁻ z, ‖v z‖ₑ ^ (3 / 2 : ℝ) ≠ ⊤) :
    ∫⁻ z, (∫⁻ w, ‖u (z + w)‖ₑ * ‖v w‖ₑ) ^ (3 : ℝ) ≤
      ((∫⁻ z, ‖u z‖ₑ ^ (3 / 2 : ℝ)) * ∫⁻ z, ‖v z‖ₑ ^ (3 / 2 : ℝ)) ^ 2 := by
  set Fu : ℝ≥0∞ := ∫⁻ z, ‖u z‖ₑ ^ (3 / 2 : ℝ) with hFudef
  set Fv : ℝ≥0∞ := ∫⁻ z, ‖v z‖ₑ ^ (3 / 2 : ℝ) with hFvdef
  have hshift : ∀ z : SpaceTime, ∫⁻ w, ‖u (z + w)‖ₑ ^ (3 / 2 : ℝ) = Fu := fun z =>
    lintegral_add_left_eq_self (fun x => ‖u x‖ₑ ^ (3 / 2 : ℝ)) z
  have hum : ∀ z : SpaceTime, Measurable (fun w => ‖u (z + w)‖ₑ) := fun z =>
    (hu.comp (measurable_const.add measurable_id)).enorm
  have hvm : Measurable (fun w => ‖v w‖ₑ) := hv.enorm
  have hpt : ∀ z : SpaceTime, (∫⁻ w, ‖u (z + w)‖ₑ * ‖v w‖ₑ) ^ (3 : ℝ) ≤
      (∫⁻ w, ‖u (z + w)‖ₑ ^ (3 / 2 : ℝ) * ‖v w‖ₑ ^ (3 / 2 : ℝ)) * Fu * Fv := by
    intro z
    have := constantsRate_lintegral_cube_le volume (hum z).aemeasurable hvm.aemeasurable
    rwa [hshift z] at this
  have hmeas2 : Measurable (fun x : SpaceTime × SpaceTime =>
      ‖u (x.1 + x.2)‖ₑ ^ (3 / 2 : ℝ) * ‖v x.2‖ₑ ^ (3 / 2 : ℝ)) := by
    have h1 : Measurable (fun x : SpaceTime × SpaceTime => ‖u (x.1 + x.2)‖ₑ) :=
      (hu.comp (measurable_fst.add measurable_snd)).enorm
    have h2 : Measurable (fun x : SpaceTime × SpaceTime => ‖v x.2‖ₑ) :=
      (hv.comp measurable_snd).enorm
    exact (h1.pow_const _).mul (h2.pow_const _)
  calc
    ∫⁻ z, (∫⁻ w, ‖u (z + w)‖ₑ * ‖v w‖ₑ) ^ (3 : ℝ) ≤
        ∫⁻ z, (∫⁻ w, ‖u (z + w)‖ₑ ^ (3 / 2 : ℝ) * ‖v w‖ₑ ^ (3 / 2 : ℝ)) * Fu * Fv :=
      lintegral_mono hpt
    _ = (∫⁻ z, ∫⁻ w, ‖u (z + w)‖ₑ ^ (3 / 2 : ℝ) * ‖v w‖ₑ ^ (3 / 2 : ℝ)) * Fu * Fv := by
      rw [lintegral_mul_const' _ _ hFv, lintegral_mul_const' _ _ hFu]
    _ = (Fu * Fv) * Fu * Fv := by
      congr 2
      rw [lintegral_lintegral_swap hmeas2.aemeasurable]
      calc
        ∫⁻ w, ∫⁻ z, ‖u (z + w)‖ₑ ^ (3 / 2 : ℝ) * ‖v w‖ₑ ^ (3 / 2 : ℝ) =
            ∫⁻ w, (∫⁻ z, ‖u (z + w)‖ₑ ^ (3 / 2 : ℝ)) * ‖v w‖ₑ ^ (3 / 2 : ℝ) := by
          apply lintegral_congr
          intro w
          rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)]
        _ = ∫⁻ w, Fu * ‖v w‖ₑ ^ (3 / 2 : ℝ) := by
          apply lintegral_congr
          intro w
          have : ∫⁻ z, ‖u (z + w)‖ₑ ^ (3 / 2 : ℝ) = Fu :=
            lintegral_add_right_eq_self (fun x => ‖u x‖ₑ ^ (3 / 2 : ℝ)) w
          rw [this]
        _ = Fu * Fv := lintegral_const_mul' _ _ hFu
    _ = (Fu * Fv) ^ 2 := by ring

end RegularityStructures.Phi43

end
