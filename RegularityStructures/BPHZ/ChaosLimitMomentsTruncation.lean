/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Time truncation of a test function

For a test function `g` on `ℝ × T³` and `c, R : ℝ`, `timeTruncation c R g` is `g` restricted to the
time slab `|y₀ - c| ≤ R`. Since the space `T³` is compact, the support of the truncation lies in
the compact set `[c - R, c + R] × T³`. As `R → ∞` the truncations converge pointwise to `g`, and
`∫ |g - timeTruncation c R g| → 0` for integrable `g`
(`tendsto_integral_abs_sub_timeTruncation`).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace RegularityStructures

/-- The restriction of `g` to the time slab `|y₀ - c| ≤ R`. -/
noncomputable def timeTruncation (c R : ℝ) (g : SpaceTime → ℝ) : SpaceTime → ℝ :=
  Set.indicator {y : SpaceTime | |y.1 - c| ≤ R} g

end RegularityStructures

end

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

theorem measurableSet_timeTruncationSlab (c R : ℝ) : MeasurableSet {y : SpaceTime | |y.1 - c| ≤ R} :=
  measurableSet_le (continuous_abs.measurable.comp (measurable_fst.sub_const c))
    measurable_const

theorem measurable_timeTruncation {g : SpaceTime → ℝ} (hg : Measurable g) (c R : ℝ) :
    Measurable (timeTruncation c R g) :=
  hg.indicator (measurableSet_timeTruncationSlab c R)

theorem timeTruncation_eq_of_le {c R : ℝ} {y : SpaceTime} (g : SpaceTime → ℝ)
    (h : |y.1 - c| ≤ R) : timeTruncation c R g y = g y :=
  Set.indicator_of_mem (show y ∈ {y : SpaceTime | |y.1 - c| ≤ R} from h) g

theorem timeTruncation_eq_zero_of_lt {c R : ℝ} {y : SpaceTime} (g : SpaceTime → ℝ)
    (h : R < |y.1 - c|) : timeTruncation c R g y = 0 :=
  Set.indicator_of_notMem (show y ∉ {y : SpaceTime | |y.1 - c| ≤ R} from not_le.2 h) g

theorem abs_le_of_timeTruncation_ne_zero {c R : ℝ} {y : SpaceTime} {g : SpaceTime → ℝ}
    (h : timeTruncation c R g y ≠ 0) : |y.1 - c| ≤ R := by
  by_contra hc
  exact h (timeTruncation_eq_zero_of_lt g (not_le.1 hc))

theorem abs_timeTruncation_le (c R : ℝ) (g : SpaceTime → ℝ) (y : SpaceTime) :
    |timeTruncation c R g y| ≤ |g y| := by
  by_cases h : |y.1 - c| ≤ R
  · rw [timeTruncation_eq_of_le g h]
  · rw [timeTruncation_eq_zero_of_lt g (not_le.1 h), abs_zero]
    exact abs_nonneg _

theorem integrable_timeTruncation {g : SpaceTime → ℝ} (hg : Integrable g) (c R : ℝ) :
    Integrable (timeTruncation c R g) :=
  hg.indicator (measurableSet_timeTruncationSlab c R)

/-- The difference of two truncations is dominated by the part of `g` beyond the smaller slab. -/
theorem abs_timeTruncation_sub_le {c R R' : ℝ} (hR : R ≤ R') (g : SpaceTime → ℝ)
    (y : SpaceTime) :
    |timeTruncation c R' g y - timeTruncation c R g y| ≤ |g y - timeTruncation c R g y| := by
  by_cases h : |y.1 - c| ≤ R
  · rw [timeTruncation_eq_of_le g h, timeTruncation_eq_of_le g (h.trans hR)]
  · rw [timeTruncation_eq_zero_of_lt g (not_le.1 h), sub_zero, sub_zero]
    exact abs_timeTruncation_le c R' g y

theorem tendsto_timeTruncation (c : ℝ) (g : SpaceTime → ℝ) (y : SpaceTime) :
    Tendsto (fun n : ℕ => timeTruncation c n g y) atTop (𝓝 (g y)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈|y.1 - c|⌉₊] with n hn
  exact (timeTruncation_eq_of_le g ((Nat.le_ceil _).trans (by exact_mod_cast hn))).symm

theorem integrable_timeTruncation_mul {c R : ℝ} {g F : SpaceTime → ℝ} (hgm : Measurable g)
    (hFm : Measurable F) (hint : Integrable (fun y => g y * F y)) :
    Integrable (fun y => timeTruncation c R g y * F y) := by
  refine Integrable.mono' hint.norm
    ((measurable_timeTruncation hgm c R).mul hFm).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_timeTruncation_le c R g y) (abs_nonneg _)

/-- Pathwise convergence of the truncated integrals. -/
theorem tendsto_integral_timeTruncation_mul {c : ℝ} {g F : SpaceTime → ℝ} (hgm : Measurable g)
    (hFm : Measurable F) (hint : Integrable (fun y => g y * F y)) :
    Tendsto (fun n : ℕ => ∫ y, timeTruncation c n g y * F y) atTop (𝓝 (∫ y, g y * F y)) := by
  refine tendsto_integral_of_dominated_convergence (fun y => ‖g y * F y‖)
    (fun n => ((measurable_timeTruncation hgm c n).mul hFm).aestronglyMeasurable) hint.norm
    (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_timeTruncation_le c n g y) (abs_nonneg _)
  · exact (tendsto_timeTruncation c g y).mul_const (F y)

/-- The `L¹` norm of the part of `g` beyond the slab tends to zero. -/
theorem tendsto_integral_abs_sub_timeTruncation {c : ℝ} {g : SpaceTime → ℝ} (hgm : Measurable g)
    (hgi : Integrable g) :
    Tendsto (fun n : ℕ => ∫ y, |g y - timeTruncation c n g y|) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := (volume : Measure SpaceTime))
    (F := fun (n : ℕ) y => |g y - timeTruncation c n g y|) (f := fun _ => (0 : ℝ))
    (fun y => |g y|)
    (fun n => (continuous_abs.measurable.comp
      (hgm.sub (measurable_timeTruncation hgm c n))).aestronglyMeasurable) hgi.abs
    (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simpa using h
  · rw [Real.norm_eq_abs, abs_abs]
    by_cases hy : |y.1 - c| ≤ n
    · rw [timeTruncation_eq_of_le g hy]
      simp
    · rw [timeTruncation_eq_zero_of_lt g (not_le.1 hy), sub_zero]
  · have := ((tendsto_timeTruncation c g y).const_sub (g y)).abs
    simpa using this

end RegularityStructures

end
