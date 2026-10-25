/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Realising.Reg
public import RegularityStructures.Abstract.Integration.Realising.Measurable
public import RegularityStructures.Abstract.Polynomial.Model.Fubini
public import RegularityStructures.Abstract.Integration.Realising.RealGerm
public import RegularityStructures.Abstract.Integration.Realising.TaylorTendsto

/-!
# The regularisations of the realised distribution

`realReg`: the `Q`-family `t ↦ Q_t g_{x,i}` of the distribution `ψ ↦ ∫ ψ(y) realGerm(y) dy`, extended
by `0` to `t ≤ 0`.

Source: [Hai14, Definition 5.9 and Remark 5.10].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The `Q`-family `t ↦ Q_t g_{x,i}` of the realised distribution
`ψ ↦ ∫ ψ(y) ∑_n (Π_x e_i)(K^{deg i}_{n;xy}) dy`, extended by `0` to `t ≤ 0`. -/
def realReg (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (x : ParabolicSpace) (i : ι) :
    ℝ → ParabolicSpace → ℝ := fun t z =>
  if 0 < t then parabolicSemigroup.apply t (realGerm M N x i) z else 0

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem realReg_of_pos (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (x : ParabolicSpace) (i : ι)
    {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    realReg M N x i t z = parabolicSemigroup.apply t (realGerm M N x i) z := by
  simp [realReg, ht]

end RegularityStructures

end
