/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorBound

/-!
# `L¹` bound for the box Taylor remainder

`exists_integral_abs_remJ_le`: if `φ` is smooth with compact support, `|s_j| ≤ d^{w_j}`, then
`∫ |remJ s m J φ| ≤ ∑_{ℓ ∈ E} d^{|ℓ|_𝔰} ∫ |D^ℓ φ|` where `E` is a finite list of derivative words
(depending on `m`, `J`) each containing at least `m_j + 1` derivatives in some direction `j ∈ J`.
Proof: induction on `J` using `remJ_cons`, the 1D remainder bound `integral_abs_remOp_le` and the
pointwise bound `exists_abs_tyOp_le`.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem contDiff_remOp {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (e : ParabolicSpace)
    (s : ℝ) (m : ℕ) : ContDiff ℝ ∞ (remOp e s m φ) := by
  rw [remOp_eq_sub]
  exact (hφ.comp (contDiff_id.add contDiff_const)).sub (contDiff_tayOp hφ e s m)

theorem lineIter_remOp {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (e : ParabolicSpace)
    (s : ℝ) (m : ℕ) (K : List ParabolicSpace) :
    lineIter K (remOp e s m φ) = remOp e s m (lineIter K φ) := by
  have hS : ContDiff ℝ ∞ fun w => φ (w + s • e) := hφ.comp (contDiff_id.add contDiff_const)
  rw [remOp_eq_sub, lineIter_sub hS (contDiff_tayOp hφ e s m), lineIter_shift,
    lineIter_tayOp hφ, remOp_eq_sub]

end RegularityStructures

end
