/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Defs
public import RegularityStructures.Abstract.Singular.Remainder.Cell
public import RegularityStructures.Abstract.Singular.Layer.Setting
public import RegularityStructures.Abstract.Singular.Kernel.Vanish
public import RegularityStructures.Abstract.Model

/-!
# Linearity of the lattice reconstruction for pieces supported in unit balls

* `latticeRecon_sum_smul`: `⟨R f, ∑ c_a g_a⟩ = ∑ c_a ⟨R f, g_a⟩` for finitely many smooth `g_a`
  supported in unit balls whose lattice approximations converge;
* `latticeRecon_add_of_causal`: adding a smooth function vanishing for `t ≥ 0` does not change the
  reconstruction.
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- `ψ` is *admissible* for the reconstruction `R f`: it is smooth, the lattice approximations
of every piece `ψ χ_{3,j}` converge, and the reconstructions of the pieces are summable. -/
structure RemSumm (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
    (ψ : ParabolicSpace → ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) ψ
  tendsto : ∀ j : LatticeIndex, Filter.Tendsto
    (M.latticeApprox f (fun y => ψ y * latticeCell 3 j y)) Filter.atTop
    (nhds (M.latticeRecon f (fun y => ψ y * latticeCell 3 j y)))
  summable : Summable (fun j : LatticeIndex => M.latticeRecon f (fun y => ψ y * latticeCell 3 j y))

end Model

end RegularityStructures

end

