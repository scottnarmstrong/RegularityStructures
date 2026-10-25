/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Structural properties of the auxiliary semigroup

`parabolicSemigroup` is symmetric (the kernel is even), `scaleDist` is a metric-like size
(`IsMetricScale`), and the kernel is jointly measurable in `(t, x, y)`
(`IsJointMeasurable`), which is the form of measurability needed for Fubini in the time variable.
-/

public section

open MeasureTheory Real

namespace RegularityStructures

/-- `(t, b) ↦ symKernel j t b` is jointly measurable. -/
theorem measurable_symKernel_uncurry (j : ℕ) :
    Measurable fun p : ℝ × ℝ => symKernel j p.1 p.2 := by
  have hf : StronglyMeasurable (Function.uncurry fun (p : ℝ × ℝ) (ξ : ℝ) =>
      Real.exp (-(p.1 * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * p.2)) :=
    Continuous.stronglyMeasurable (by fun_prop)
  exact (hf.integral_prod_right).measurable

theorem measurable_parabolicKernel_uncurry :
    Measurable fun p : ℝ × ParabolicSpace => parabolicKernel p.1 p.2 := by
  unfold parabolicKernel
  have h1 : Measurable fun p : ℝ × ParabolicSpace => heatKernel1D p.1 p.2.1 :=
    (measurable_symKernel_uncurry 1).comp (measurable_fst.prodMk (measurable_snd.fst))
  have h2 : ∀ i : Fin 3, Measurable fun p : ℝ × ParabolicSpace => quarticKernel p.1 (p.2.2 i) :=
    fun i => (measurable_symKernel_uncurry 2).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd.snd))
  exact h1.mul (Finset.measurable_prod _ fun i _ => h2 i)

theorem parabolicSemigroup_isSymmetric : parabolicSemigroup.IsSymmetric := by
  intro t x y
  show parabolicKernel t (x - y) = parabolicKernel t (y - x)
  rw [← parabolicKernel_neg t (x - y), neg_sub]

theorem parabolicSemigroup_isMetricScale : parabolicSemigroup.IsMetricScale where
  symm x y := parabolicNorm_sub_comm x y
  triangle x y z := by
    show parabolicNorm (x - z) ≤ parabolicNorm (x - y) + parabolicNorm (y - z)
    have := parabolicNorm_add_le (x - y) (y - z)
    rwa [sub_add_sub_cancel] at this

theorem parabolicSemigroup_isJointMeasurable : parabolicSemigroup.IsJointMeasurable := by
  show Measurable fun p : ℝ × ParabolicSpace × ParabolicSpace => parabolicKernel p.1 (p.2.1 - p.2.2)
  exact measurable_parabolicKernel_uncurry.comp
    (measurable_fst.prodMk (measurable_snd.fst.sub measurable_snd.snd))

end RegularityStructures

end
