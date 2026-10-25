/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Weighted.Operator
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs
public import RegularityStructures.Analysis.Semigroup.Weighted.Coherent
public import RegularityStructures.Analysis.Semigroup.Operator
public import RegularityStructures.Analysis.Semigroup.OperatorBound

/-!
# The semigroup on weighted functions

Integrability of `Q_t(x, ·) g` and the semigroup identity for `g` bounded by a moderate weight.

Source: [Hos25, Section 4].
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
  {ρ : E → ℝ} {p : ℝ}

theorem integrable_kernel_mul_of_weight_bound (hρ : K.IsModerateWeight ρ p) {t : ℝ} (ht : 0 < t)
    (x : E) {g : E → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B * ρ y) :
    Integrable (fun y => K.kernel t x y * g y) μ := by
  refine Integrable.mono' ((K.integrable_abs_kernel_mul_weight hρ ht x).mul_const B)
    ((K.measurable_kernel_right t x).mul hg).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |K.kernel t x y| * |g y| ≤ |K.kernel t x y| * (B * ρ y) :=
        mul_le_mul_of_nonneg_left (hB y) (abs_nonneg _)
    _ = _ := by ring

theorem apply_apply_of_weight_bound [SFinite μ] (hρ : K.IsModerateWeight ρ p) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) {g : E → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ y, |g y| ≤ B * ρ y) (x : E) :
    K.apply s (K.apply t g) x = K.apply (s + t) g x := by
  have hmeas : Measurable (fun p : E × E => K.kernel s x p.1 * (K.kernel t p.1 p.2 * g p.2)) :=
    ((K.measurable_kernel_right s x).comp measurable_fst).mul
      ((K.measurable_kernel t).mul (hg.comp measurable_snd))
  have hint : Integrable (fun p : E × E =>
      K.kernel s x p.1 * (K.kernel t p.1 p.2 * g p.2)) (μ.prod μ) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · dsimp only
      exact (K.integrable_kernel_mul_of_weight_bound hρ ht y hg hB).const_mul _
    · refine Integrable.mono' ((K.integrable_abs_kernel_mul_weight hρ hs x).mul_const
          (B * K.weightConst p t))
        hmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      have e : ∫ z, ‖K.kernel s x y * (K.kernel t y z * g z)‖ ∂μ =
          |K.kernel s x y| * ∫ z, |K.kernel t y z * g z| ∂μ := by
        rw [← integral_const_mul]
        simp only [Real.norm_eq_abs, abs_mul]
      have hnn : 0 ≤ ∫ z, ‖K.kernel s x y * (K.kernel t y z * g z)‖ ∂μ :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn, e]
      calc |K.kernel s x y| * ∫ z, |K.kernel t y z * g z| ∂μ
          ≤ |K.kernel s x y| * (B * ρ y * K.weightConst p t) :=
            mul_le_mul_of_nonneg_left (K.integral_abs_kernel_mul_le_of_weight_bound hρ ht y hB)
              (abs_nonneg _)
        _ = _ := by ring
  calc K.apply s (K.apply t g) x
      = ∫ y, ∫ z, K.kernel s x y * (K.kernel t y z * g z) ∂μ ∂μ := by
        simp only [apply, ← integral_const_mul]
    _ = ∫ z, ∫ y, K.kernel s x y * (K.kernel t y z * g z) ∂μ ∂μ :=
        integral_integral_swap (f := fun y z => K.kernel s x y * (K.kernel t y z * g z)) hint
    _ = ∫ z, K.kernel (s + t) x z * g z ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [← K.semigroup hs ht x z, ← integral_mul_const]
        simp only [mul_assoc]
    _ = K.apply (s + t) g x := rfl

end RegularityStructures.RegularisingSemigroup

end
