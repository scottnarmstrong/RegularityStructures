/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointBounds
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The operator bound for a model distance `δ ≥ 0`

`Model.singularDiffBoundOn_phi4_causalOperator` is proved for `δ > 0` (the two-model Theorem 7.1 is
stated with a positive size of the model difference). Since the model-difference constants may
always be enlarged, and the bound is closed in the constant (`SingularDiffBoundOn.of_forall_lt`),
the statement holds for `δ ≥ 0`: `Model.singularDiffBoundOn_phi4_causalOperator_of_nonneg`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

theorem piDiffBoundOn_mono {M₁ M₂ : Model 𝒯 parabolicSemigroup} {γ C C' : ℝ} {S : Set ParabolicSpace}
    (h : M₁.PiDiffBoundOn M₂ γ C S) (hC : C ≤ C') : M₁.PiDiffBoundOn M₂ γ C' S :=
  fun i hi t ht x hx => (h i hi t ht x hx).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.1.le _))

end Model

end RegularityStructures

end
