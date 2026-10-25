/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition
public import RegularityStructures.Analysis.Heat.Schauder.Reflect

/-!
# `L¹` scaling of the heat shells and their generators

`heatShell n = 2^{-2n} · (heatShell 0)^{2^{-n}}` (rescaled at scale `2^{-n}`), so
`∫ |heatShell n| = 2^{-2n} ∫ |heatShell 0|` and `∫ |L heatShell n| = 2^{2n} ∫ |L heatShell 0|`
(`L = parabolicGenerator`).  These are the `B₀`, `B₁` of the pairing bound
`abs_pairing_reflect_le`.

Source: Hairer, arXiv:1303.5113v4, Lemma 5.5 (scaling of the shells).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem parabolicGenerator_const_mul {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    parabolicGenerator (fun w => a * f w) = fun w => a * parabolicGenerator f w := by
  funext w
  have hk : ∀ k : ℕ, ContDiff ℝ k f := fun k => hf.of_le (by exact_mod_cast le_top)
  have e : ∀ k : ℕ, ∀ v : ParabolicSpace, iteratedFDeriv ℝ k (fun w => a * f w) w (fun _ => v) =
      a * iteratedFDeriv ℝ k f w (fun _ => v) := by
    intro k v
    have hs : (fun w => a * f w) = a • f := by funext; simp
    have := iteratedFDeriv_const_smul_apply (a := a) (hk k).contDiffAt (x := w) (i := k)
    rw [hs]
    simpa using congrArg (fun m => m (fun _ => v)) this
  unfold parabolicGenerator
  simp only [e, ← Finset.mul_sum]
  ring

end RegularityStructures

end
