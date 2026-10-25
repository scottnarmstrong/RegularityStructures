/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.TestFunction
public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Existence of test functions

`exists_mem_testFunctionClass`: for every `r`, the test-function class `testFunctionClass r`
contains a function with `∫ φ > 0`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

end RegularityStructures

end

public section

namespace RegularityStructures

/-- A small `ContDiffBump` on parabolic space, supported in the closed unit parabolic ball. -/
noncomputable def smallBump : ContDiffBump (0 : ParabolicSpace) where
  rIn := 1 / 32
  rOut := 1 / 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem parabolicNorm_le_of_norm_lt {w : ParabolicSpace} {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 16)
    (h : ‖w‖ < R) : parabolicNorm w ≤ 1 := by
  have h1 : |w.1| < R := by
    have := (Prod.norm_def w ▸ le_max_left ‖w.1‖ ‖w.2‖).trans_lt h
    simpa using this
  have h2 : ∀ i, |w.2 i| < R := fun i => by
    have := ((norm_le_pi_norm w.2 i).trans (Prod.norm_def w ▸ le_max_right ‖w.1‖ ‖w.2‖)).trans_lt h
    simpa using this
  have h3 : Real.sqrt |w.1| ≤ 1 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have h4 : ∑ i, |w.2 i| ≤ 3 * (1 / 16) := by
    calc ∑ i, |w.2 i| ≤ ∑ _i : Fin 3, (1 / 16 : ℝ) :=
          Finset.sum_le_sum fun i _ => ((h2 i).le.trans hR1)
      _ = 3 * (1 / 16) := by simp
  unfold parabolicNorm
  linarith

open scoped ContDiff in
theorem exists_mem_testFunctionClass (r : ℕ) :
    ∃ φ ∈ testFunctionClass r, 0 < ∫ w, φ w := by
  set f : ParabolicSpace → ℝ := ⇑smallBump
  have hf : ContDiff ℝ ∞ f := smallBump.contDiff
  have hcs : HasCompactSupport f := smallBump.hasCompactSupport
  obtain ⟨C, hC0, hC⟩ := hcs.exists_bound_iteratedFDeriv hf r
  have hpos : (0 : ℝ) < (C + 1)⁻¹ := by positivity
  refine ⟨(C + 1)⁻¹ • f, ⟨hf.const_smul ((C + 1)⁻¹ : ℝ), ?_, ?_⟩, ?_⟩
  · intro w hw
    have : f w = 0 := by
      refine smallBump.zero_of_le_dist ?_
      by_contra hlt
      replace hlt := not_le.1 hlt
      have hro : smallBump.rOut = 1 / 16 := rfl
      have := parabolicNorm_le_of_norm_lt (w := w) (R := 1 / 16) (by norm_num) le_rfl
        (by simpa [dist_zero_right, hro] using hlt)
      linarith
    simp [this]
  · intro k hk w
    rw [iteratedFDeriv_const_smul_apply ((hf.of_le (mod_cast le_top)).contDiffAt), norm_smul, Real.norm_of_nonneg hpos.le]
    calc (C + 1)⁻¹ * ‖iteratedFDeriv ℝ k f w‖ ≤ (C + 1)⁻¹ * C :=
          mul_le_mul_of_nonneg_left (hC k hk w) hpos.le
      _ ≤ 1 := by
        rw [inv_mul_le_iff₀ (by positivity)]
        linarith
  · have hint : MeasureTheory.Integrable f := hf.continuous.integrable_of_hasCompactSupport hcs
    have hpos' : 0 < ∫ w, f w := by
      refine (MeasureTheory.integral_pos_iff_support_of_nonneg (fun w => smallBump.nonneg) hint).2 ?_
      rw [smallBump.support_eq]
      exact Metric.measure_ball_pos _ _ smallBump.rOut_pos
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [MeasureTheory.integral_const_mul]
    exact mul_pos hpos hpos'

end RegularityStructures

end
