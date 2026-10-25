/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG
public import RegularityStructures.Abstract.Singular.Remainder.GammaG
public import RegularityStructures.Abstract.Model

/-!
# Basic API for `remVecG`

Generic-kernel version of `Model.remVec_sub_gammaMap_apply_of_notMem_range`: `R_γ f` has only
polynomial components (`remVecG_mem_subspace` is in
`RegularityStructures.Abstract.Singular.Remainder.GammaG`).
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

/-- `R_γ f(y) − Γ_{yx} R_γ f(x)` has only polynomial components. -/
theorem remVecG_sub_gammaMap_apply_of_notMem_range (M : Model 𝒯 parabolicSemigroup)
    (r : ParabolicSpace → ℝ) (P : PolynomialSector 𝒯 N') (γ : ℝ) (f : ParabolicSpace → ι → ℝ)
    (x y : ParabolicSpace) {j : ι} (hj : j ∉ Set.range P.emb) :
    (M.remVecG r P γ f y - M.gammaMap y x (M.remVecG r P γ f x)) j = 0 := by
  have hpoly : ∀ v ∈ P.subspace, v j = 0 := fun v hv => hv j hj
  have h1 := hpoly _ (M.remVecG_mem_subspace r P γ f y)
  have h2 : M.gammaMap y x (M.remVecG r P γ f x) j = 0 :=
    hpoly _ (P.invariant _ (M.gamma y x).2 _ (M.remVecG_mem_subspace r P γ f x))
  rw [Pi.sub_apply, h1, h2, sub_zero]

end Model

end RegularityStructures

end
