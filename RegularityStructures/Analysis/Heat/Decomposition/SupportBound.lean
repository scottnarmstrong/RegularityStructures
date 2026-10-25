/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Support
public import RegularityStructures.Analysis.Heat.Decomposition.Basic
public import RegularityStructures.Analysis.Heat.Decomposition.LineIter
public import RegularityStructures.Analysis.Parabolic.TestFunctionExists

/-!
# Support and derivative bounds of the heat shells

The heat shells have compact support (`hasCompactSupport_heatShell`) and bounded derivatives
(`exists_abs_lineIter_heatShell_le`).

Source: [Hai14, Lemma 5.5].
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem hasCompactSupport_heatShell (n : ℕ) : HasCompactSupport (heatShell n) :=
  HasCompactSupport.intro (isCompact_parabolicNorm_le ((2 : ℝ)⁻¹ ^ n)) fun _ hz =>
    heatShell_eq_zero (not_le.1 hz)

theorem exists_abs_lineIter_heatShell_le (L : List ParabolicSpace) (n : ℕ) :
    ∃ B, ∀ w, |lineIter L (heatShell n) w| ≤ B := by
  obtain ⟨B, hB⟩ := ((contDiff_lineIter (contDiff_heatShell n) L).continuous.bounded_above_of_compact_support
    (hasCompactSupport_lineIter (hasCompactSupport_heatShell n) L))
  exact ⟨B, fun w => by simpa using hB w⟩

end RegularityStructures

end
