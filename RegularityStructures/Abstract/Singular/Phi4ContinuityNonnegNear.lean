/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Phi4ContinuityNonneg
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.Singular.Phi4ContinuityNonneg`

The statements of `RegularityStructures.Abstract.Singular.Phi4ContinuityNonneg` that involve
`Γ`-bounds, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

theorem gammaDiffBoundOn_mono_near {M₁ M₂ : Model 𝒯 parabolicSemigroup} {γ C C' : ℝ}
    {S : Set ParabolicSpace} (h : M₁.GammaDiffNearOn M₂ γ C S) (hC : C ≤ C') :
    M₁.GammaDiffNearOn M₂ γ C' S :=
  fun i j hi hj x hx y hy hxy => (h i j hi hj x hx y hy hxy).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _))

end Model

end RegularityStructures

end
