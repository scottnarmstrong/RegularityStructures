/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Gamma
public import RegularityStructures.Abstract.Singular.Remainder.TaylorQuant
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorDeriv

/-!
# Increments of `R_γ f`

Hairer, arXiv:1303.5113v4, Lemma 7.7 (smooth part), the increment bound: for `x, y` with
`x₀, y₀ ≤ T ≤ 1`, `d = ‖y − x‖_𝔰 ≤ 1`, and `|k|_𝔰 < γ + 2`,

  `|(R_γ f(y) − Γ_{yx} R_γ f(x))_{X^k}| ≤ C K₀ Cf d^{γ + 2 − |k|_𝔰}`
  (`exists_abs_remVec_sub_gammaMap_le`).

The component is `(1/k!)` times the pairing of `R f` with the Taylor remainder kernel
`D^k R(y − ·) − ∑_{|l|_𝔰 < γ+2−|k|_𝔰} (y−x)^l/l! D^{k+l} R(x − ·)`, whose scaled derivatives are
`≲ d^{γ+2−|k|}` times a spatial decay by the quantitative Taylor bounds.
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem lineIter_multiDirs_lineIter {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (k l : Fin 4 →₀ ℕ) :
    lineIter (multiDirs l) (lineIter (multiDirs k) φ) = lineIter (multiDirs (k + l)) φ := by
  rw [lineIter_perm hφ (multiDirs_add_perm k l), lineIter_append]

end RegularityStructures

end
