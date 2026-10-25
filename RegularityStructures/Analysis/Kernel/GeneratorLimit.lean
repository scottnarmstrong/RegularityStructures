/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorDiff
public import RegularityStructures.Analysis.Kernel.GeneratorProps

/-!
# The approximate identity: `∫ q_v(z - y) φ(y) dy → φ(z)` as `v ↓ 0`

`∫ q_v = 1`, `|φ(y) - φ(z)| ≤ C ‖y - z‖_𝔰` for `φ` smooth with compact support, and the first
moment bound `∫ |q_v(z - y)| ‖y - z‖_𝔰 dy ≤ M₁ v^{1/4}`.
-/

public section

open MeasureTheory Filter Topology Real
open scoped ContDiff

namespace RegularityStructures

theorem integrable_parabolicKernel {t : ℝ} (ht : 0 < t) : Integrable (parabolicKernel t) := by
  have h := integrable_parabolicKernelWeight ht (le_refl (0 : ℝ)) (e := 0) (fun _ => le_rfl)
  refine h.mono' (measurable_parabolicKernel t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  unfold parabolicKernelWeight parabolicKernel
  simp only [Real.rpow_zero, mul_one, Pi.zero_apply, Real.norm_eq_abs, abs_mul, Finset.abs_prod]
  exact le_rfl

theorem integrable_parabolicKernel_sub {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    Integrable fun y => parabolicKernel t (z - y) := by
  have h : Integrable (fun y : ParabolicSpace => parabolicKernel t (y - z)) volume := by
    have h0 := integrable_parabolicKernel ht
    rw [Measure.volume_eq_prod] at h0 ⊢
    exact h0.comp_sub_right z
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show parabolicKernel t (y - z) = parabolicKernel t (z - y)
  rw [← parabolicKernel_neg t (y - z), neg_sub]

theorem integral_parabolicKernel_sub {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    ∫ y, parabolicKernel t (z - y) = 1 := by
  have e : ∀ y : ParabolicSpace, parabolicKernel t (z - y) = parabolicKernel t (y - z) :=
    fun y => by rw [← parabolicKernel_neg t (y - z), neg_sub]
  simp_rw [e]
  have : ∫ y : ParabolicSpace, parabolicKernel t (y - z) = ∫ w : ParabolicSpace, parabolicKernel t w := by
    rw [Measure.volume_eq_prod]
    exact integral_sub_right_eq_self (fun w : ParabolicSpace => parabolicKernel t w) z
  rw [this, integral_parabolicKernel ht]

end RegularityStructures

end
