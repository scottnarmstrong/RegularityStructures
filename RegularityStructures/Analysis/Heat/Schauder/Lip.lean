/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorLip
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
public import RegularityStructures.Analysis.Heat.Decomposition.Support
public import RegularityStructures.Analysis.Heat.Decomposition.SupportBound
public import RegularityStructures.Analysis.Semigroup.Pairing.LocalOrder

/-!
# `L¹` modulus of continuity of a compactly supported smooth function

If `g` is smooth and vanishes outside the unit parabolic ball then
`∫ |g(u) - g(u - a)| du ≤ M ‖a‖_𝔰` for `‖a‖_𝔰 ≤ 1` (`exists_integral_abs_sub_le`).  Used to compare
the shells `heatShell n (x - ·)` and `heatShell n (y - ·)` in the Hölder estimate.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem exists_integral_abs_sub_le {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : ∀ w, 1 < parabolicNorm w → g w = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ParabolicSpace, parabolicNorm a ≤ 1 →
      ∫ u, |g u - g (u - a)| ≤ M * parabolicNorm a := by
  have hc : HasCompactSupport g := hasCompactSupport_of_eq_zero_unit hs
  obtain ⟨C, hC, hCb⟩ := exists_abs_sub_le_parabolicNorm hg hc
  set B2 := {u : ParabolicSpace | parabolicNorm u ≤ 2} with hB2
  have hmeas : MeasurableSet B2 :=
    (isClosed_le continuous_parabolicNorm continuous_const).measurableSet
  have hfin : volume B2 < ⊤ := (isCompact_parabolicNorm_le 2).measure_lt_top
  refine ⟨C * (volume B2).toReal, mul_nonneg hC ENNReal.toReal_nonneg, fun a ha => ?_⟩
  have hcont : Continuous fun u => |g u - g (u - a)| :=
    (hg.continuous.sub (hg.continuous.comp (continuous_id.sub continuous_const))).abs
  have hout : ∀ u, 2 < parabolicNorm u → |g u - g (u - a)| = 0 := by
    intro u hu
    have h1 : 1 < parabolicNorm u - parabolicNorm a := by linarith
    have h2 : parabolicNorm u ≤ parabolicNorm (u - a) + parabolicNorm a := by
      simpa using parabolicNorm_add_le (u - a) a
    rw [hs u (by linarith), hs (u - a) (by linarith)]
    simp
  have hsupp : HasCompactSupport fun u => |g u - g (u - a)| :=
    hasCompactSupport_of_eq_zero (c := 2) (by norm_num) 0 fun u hu => hout u (by simpa using hu)
  have hint : Integrable fun u => |g u - g (u - a)| := hcont.integrable_of_hasCompactSupport hsupp
  have hind : Integrable (B2.indicator fun _ => C * parabolicNorm a) :=
    (integrable_indicator_iff hmeas).2 (integrableOn_const hfin.ne)
  have hle : ∀ u, |g u - g (u - a)| ≤ B2.indicator (fun _ => C * parabolicNorm a) u := by
    intro u
    by_cases hu : u ∈ B2
    · rw [Set.indicator_of_mem hu]
      simpa using hCb u (u - a) |>.trans_eq (by simp)
    · rw [Set.indicator_of_notMem hu, hout u (by simpa [hB2] using hu)]
  refine (integral_mono hint hind hle).trans ?_
  rw [integral_indicator_const _ hmeas, smul_eq_mul]
  refine le_of_eq ?_
  simp only [Measure.real]
  ring

end RegularityStructures

end
