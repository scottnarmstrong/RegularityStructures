/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The mollifier class is nonempty

Theorem A quantifies over the mollifiers `ρ` with `IsMollifier ρ`, so its premises are jointly
satisfiable only if this class is inhabited. A normalised smooth bump on `ℝ × ℝ³` is a mollifier.
-/

open MeasureTheory RegularityStructures.Phi43

theorem Regression.exists_mollifier : ∃ ρ : ℝ × (Fin 3 → ℝ) → ℝ, IsMollifier ρ := by
  let f : ContDiffBump (0 : ℝ × (Fin 3 → ℝ)) := ⟨1, 2, by norm_num, by norm_num⟩
  exact ⟨f.normed volume, ⟨f.contDiff_normed, f.hasCompactSupport_normed, f.integral_normed⟩⟩
