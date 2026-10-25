/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Increment
public import RegularityStructures.Abstract.Singular.Remainder.GammaG
public import RegularityStructures.Abstract.Singular.Remainder.TaylorQuant
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorDeriv
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Increments of `R_γ f`

Hairer, arXiv:1303.5113v4, Lemma 7.7 (smooth part), the increment bound: for `x, y` with
`x₀, y₀ ≤ T ≤ 1`, `d = ‖y − x‖_𝔰 ≤ 1`, and `|k|_𝔰 < γ + 2`,

  `|(R_γ f(y) − Γ_{yx} R_γ f(x))_{X^k}| ≤ C K₀ Cf d^{γ + 2 − |k|_𝔰}`
  (`exists_abs_remVec_sub_gammaMap_le_growth`).

The component is `(1/k!)` times the pairing of `R f` with the Taylor remainder kernel
`D^k R(y − ·) − ∑_{|l|_𝔰 < γ+2−|k|_𝔰} (y−x)^l/l! D^{k+l} R(x − ·)`, whose scaled derivatives are
`≲ d^{γ+2−|k|}` times a spatial decay by the quantitative Taylor bounds.
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem RemKernel.taylorProfile_lineIter_sub_apply {r : ParabolicSpace → ℝ} (hr : RemKernel r)
    (k : Fin 4 →₀ ℕ) (σ : ℝ) (x y w : ParabolicSpace) :
    taylorProfile (lineIter (multiDirs k) r) σ (y - x) (x - w) =
      lineIter (multiDirs k) r (y - w) -
        ∑ l ∈ taylorIdx σ, coeffT (parabolicCoords (y - x)) l *
          lineIter (multiDirs (k + l)) r (x - w) := by
  unfold taylorProfile
  rw [show x - w + (y - x) = y - w by abel]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [evalParabolic_monomial_div, lineIter_multiDirs_lineIter hr.contDiff k l]

theorem RemKernel.taylorProfile_lineIter_sub_eq_zero {r : ParabolicSpace → ℝ} (hr : RemKernel r)
    (k : Fin 4 →₀ ℕ) (σ : ℝ) {x y w : ParabolicSpace} (hx : x.1 ≤ w.1) (hy : y.1 ≤ w.1) :
    taylorProfile (lineIter (multiDirs k) r) σ (y - x) (x - w) = 0 := by
  rw [hr.taylorProfile_lineIter_sub_apply, hr.lineIter_sub_eq_zero _ hy, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [hr.lineIter_sub_eq_zero _ hx, mul_zero]

end RegularityStructures

end
