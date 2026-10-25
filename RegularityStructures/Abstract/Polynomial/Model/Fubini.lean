/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Growth

/-!
# The semigroup property on polynomially bounded functions

`Q_s Q_t g = Q_{s+t} g` for a polynomially bounded function `g` (Fubini and
`integral_parabolicKernel_mul_parabolicKernel`), the analogue of `RegularisingSemigroup.apply_apply`
for unbounded `g`.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {g : ParabolicSpace → ℝ}

theorem PolyBounded.apply_apply (hg : PolyBounded g) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : ParabolicSpace) :
    parabolicSemigroup.apply s (parabolicSemigroup.apply t g) x =
      parabolicSemigroup.apply (s + t) g x := by
  obtain ⟨hm, B, n, hB⟩ := hg
  have hk : ∀ (r : ℝ) (a : ParabolicSpace), Measurable fun p : ParabolicSpace × ParabolicSpace =>
      parabolicKernel r (a - p.1) := fun r a =>
    (measurable_parabolicKernel r).comp (measurable_const.sub measurable_fst)
  have hmeas : Measurable (fun p : ParabolicSpace × ParabolicSpace =>
      parabolicKernel s (x - p.1) * (parabolicKernel t (p.1 - p.2) * g p.2)) :=
    (hk s x).mul (((measurable_parabolicKernel t).comp (measurable_fst.sub measurable_snd)).mul
      (hm.comp measurable_snd))
  have hint : Integrable (fun p : ParabolicSpace × ParabolicSpace =>
      parabolicKernel s (x - p.1) * (parabolicKernel t (p.1 - p.2) * g p.2))
      (volume.prod volume) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · have := (integrable_parabolicKernel_mul_of_bound hm hB ht y).const_mul
        (parabolicKernel s (x - y))
      simpa only [mul_assoc] using this
    · refine Integrable.mono'
        (((integrable_abs_kernel_mul_pow hs n x).mul_const (B * kernelPowMoment n t)))
        hmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      have e : ∫ z, ‖parabolicKernel s (x - y) * (parabolicKernel t (y - z) * g z)‖ =
          |parabolicKernel s (x - y)| * ∫ z, |parabolicKernel t (y - z) * g z| := by
        rw [← integral_const_mul]
        simp only [Real.norm_eq_abs, abs_mul]
      have hnn : 0 ≤ ∫ z, ‖parabolicKernel s (x - y) * (parabolicKernel t (y - z) * g z)‖ :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn, e]
      calc |parabolicKernel s (x - y)| * ∫ z, |parabolicKernel t (y - z) * g z|
          ≤ |parabolicKernel s (x - y)| * (B * ((1 + parabolicNorm y) ^ n * kernelPowMoment n t)) :=
            mul_le_mul_of_nonneg_left (integral_abs_parabolicKernel_mul_le hm hB ht y)
              (abs_nonneg _)
        _ = _ := by ring
  calc parabolicSemigroup.apply s (parabolicSemigroup.apply t g) x
      = ∫ y, ∫ z, parabolicKernel s (x - y) * (parabolicKernel t (y - z) * g z) := by
        simp only [RegularisingSemigroup.apply, ← integral_const_mul]
        rfl
    _ = ∫ z, ∫ y, parabolicKernel s (x - y) * (parabolicKernel t (y - z) * g z) :=
        integral_integral_swap
          (f := fun y z => parabolicKernel s (x - y) * (parabolicKernel t (y - z) * g z)) hint
    _ = ∫ z, parabolicKernel (s + t) (x - z) * g z := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        dsimp only
        rw [← integral_parabolicKernel_mul_parabolicKernel hs ht x z, ← integral_mul_const]
        simp only [mul_assoc]
    _ = parabolicSemigroup.apply (s + t) g x := rfl

end RegularityStructures

end
