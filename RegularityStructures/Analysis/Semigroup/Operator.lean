/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The operators `Q_t` of a regularising semigroup

Basic analysis of `K.apply t g (x) = ∫ Q_t(x, y) g(y) dy` on bounded measurable functions:

* `integrable_kernel`, `integral_abs_kernel_le`: `∫ |Q_t(x, y)| dy ≤ M₀` (the `r = 0` moment);
* `abs_apply_le`: `|Q_t g| ≤ M₀ ‖g‖_∞`;
* `measurable_apply`: `Q_t g` is measurable;
* `apply_apply`: `Q_s Q_t g = Q_{s+t} g` (Fubini and the semigroup property);
* `eq_of_abs_sub_le`: two `Q`-distributions with `|Λ_t - Λ'_t| ≤ C t^β`, `β > 0`, coincide.

Source: [Hos25] = arXiv:2310.07396v2, proof of Theorem 4.1.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

theorem measurable_kernel_right (t : ℝ) (x : E) : Measurable (K.kernel t x) :=
  (K.measurable_kernel t).comp measurable_prodMk_left

theorem integrable_kernel {t : ℝ} (ht : 0 < t) (x : E) : Integrable (K.kernel t x) μ := by
  have h := K.integrable_moment ht (le_refl (0 : ℝ)) x
  simp only [Real.rpow_zero, mul_one] at h
  exact (integrable_norm_iff (K.measurable_kernel_right t x).aestronglyMeasurable).1
    (by simpa using h)

theorem integral_abs_kernel_le {t : ℝ} (ht : 0 < t) (x : E) :
    ∫ y, |K.kernel t x y| ∂μ ≤ K.momentConst 0 := by
  have h := K.moment_le ht (le_refl (0 : ℝ)) x
  simpa using h

theorem measurable_apply [SFinite μ] (t : ℝ) {g : E → ℝ} (hg : Measurable g) :
    Measurable (K.apply t g) := by
  have h : Measurable (Function.uncurry fun x y => K.kernel t x y * g y) :=
    (K.measurable_kernel t).mul (hg.comp measurable_snd)
  exact h.stronglyMeasurable.integral_prod_right.measurable

end RegularityStructures.RegularisingSemigroup

end
