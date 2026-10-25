/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Realising.Germ
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Measurability of the germ

`y ↦ ⟨Λ, K^α_{n;xy}⟩` is measurable: it is the pointwise limit, along `s = 1/(m+1)`, of the
parametric integrals `y ↦ ∫ Λ_s(z) K^α_{n;xy}(z) dz` (`tendsto_integral_taylorKernel`), and
`(y, z) ↦ K^α_{n;xy}(z)` is jointly continuous. Hence the sum over `n`, the germ `realGerm`,
is measurable (`measurable_realGerm`).
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

theorem continuous_taylorKernel_uncurry {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (n : ℕ)
    (σ : ℝ) (x : ParabolicSpace) :
    Continuous fun p : ParabolicSpace × ParabolicSpace => taylorKernel h n σ x p.1 p.2 := by
  have hg := contDiff_scaledShell h0 n
  unfold taylorKernel
  refine ((hg.continuous.comp (continuous_fst.sub continuous_snd))).sub
    (continuous_finsetSum _ fun k _ => ?_)
  exact (((continuous_evalParabolic _).comp (continuous_fst.sub continuous_const)).div_const
    _).mul ((contDiff_lineIter hg _).continuous.comp (continuous_const.sub continuous_snd))

end RegularityStructures

end
