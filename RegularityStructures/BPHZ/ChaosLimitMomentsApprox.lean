/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDense
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite-range sampling maps

* `exists_sampling_sequence`: for a closed nonempty set `S` of space-time there are measurable maps
  `πₙ` with finite range inside `S` and `πₙ x → x` for all `x ∈ S` (from `SimpleFunc.approxOn`);
* `integral_mul_comp_eq_sum`: for a map `π` with values in a finite set `T`,
  `∫ a(x) f(π x) = ∑_{b ∈ T} f(b) ∫_{π ⁻¹ {b}} a`.
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

/-- **Finite-range sampling maps** converging pointwise to the identity on a closed set. -/
theorem exists_sampling_sequence {S : Set SpaceTime} (hS : S.Nonempty) :
    ∃ π : ℕ → SpaceTime → SpaceTime, (∀ n, Measurable (π n)) ∧
      (∀ n, (Set.range (π n)).Finite) ∧ (∀ n x, π n x ∈ S) ∧
      ∀ x ∈ S, Tendsto (fun n => π n x) atTop (𝓝 x) := by
  obtain ⟨y₀, hy₀⟩ := hS
  refine ⟨fun n => SimpleFunc.approxOn id measurable_id S y₀ hy₀ n, fun n => SimpleFunc.measurable _,
    fun n => SimpleFunc.finite_range _, fun n x => SimpleFunc.approxOn_mem _ _ _ _, ?_⟩
  intro x hx
  exact SimpleFunc.tendsto_approxOn measurable_id hy₀ (subset_closure hx)

variable {β : Type*} [MeasurableSpace β]

omit [MeasurableSpace β] in
/-- Pointwise expansion of `a x * f (π x)` over the fibres of a finitely-valued map. -/
theorem mul_comp_eq_sum_indicator {π : β → SpaceTime} (T : Finset SpaceTime)
    (hT : ∀ x, π x ∈ T) (a : β → ℝ) (f : SpaceTime → ℝ) (x : β) :
    a x * f (π x) = ∑ b ∈ T, f b * (π ⁻¹' {b}).indicator a x := by
  have h1 : ∀ b, f b * (π ⁻¹' {b}).indicator a x = if π x = b then f b * a x else 0 := by
    intro b
    by_cases h : π x = b <;> simp [h]
  simp_rw [h1]
  rw [Finset.sum_ite_eq]
  simp [hT x, mul_comm]

/-- Multiplying an integrable function by `f ∘ π` for a finitely-valued measurable `π`
preserves integrability. -/
theorem integrable_mul_comp {ν : Measure β} {π : β → SpaceTime} (hπ : Measurable π)
    (T : Finset SpaceTime) (hT : ∀ x, π x ∈ T) {a : β → ℝ} (ha : Integrable a ν)
    (f : SpaceTime → ℝ) : Integrable (fun x => a x * f (π x)) ν := by
  simp_rw [mul_comp_eq_sum_indicator T hT a f]
  exact integrable_finsetSum _ fun b _ =>
    (ha.indicator (hπ (measurableSet_singleton b))).const_mul _

/-- Integral against a finitely-valued sampling map as a finite sum over the fibres. -/
theorem integral_mul_comp_eq_sum {ν : Measure β} {π : β → SpaceTime} (hπ : Measurable π)
    (T : Finset SpaceTime) (hT : ∀ x, π x ∈ T) {a : β → ℝ} (ha : Integrable a ν)
    (f : SpaceTime → ℝ) :
    ∫ x, a x * f (π x) ∂ν = ∑ b ∈ T, f b * ∫ x in π ⁻¹' {b}, a x ∂ν := by
  have hm : ∀ b : SpaceTime, MeasurableSet (π ⁻¹' {b}) := fun b =>
    hπ (measurableSet_singleton b)
  simp_rw [mul_comp_eq_sum_indicator T hT a f]
  rw [integral_finsetSum _ fun b _ => (ha.indicator (hm b)).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_indicator (hm b)]

end RegularityStructures

end
