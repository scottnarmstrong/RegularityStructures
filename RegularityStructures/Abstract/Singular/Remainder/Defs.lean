/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox
public import RegularityStructures.Abstract.Polynomial.Basic
public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Analysis.Heat.Causal.Basic
public import RegularityStructures.Analysis.Parabolic.SingularKernel
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The lift of the smooth remainder `R = G − K` to singular modelled distributions

[Hai14] = arXiv:1303.5113v4, (7.7): `R_γ f(x) = ∑_{|k|_𝔰 < γ + 2} X^k / k! ⟨R f, D^k R(x − ·)⟩`
with the smooth remainder `R = annRemainderC N`.  The test functions `D^k R(x − ·)` are not
compactly supported in space, so the pairing with the lattice reconstruction `Model.latticeRecon`
is taken cell by cell (level-3 lattice cells, `Model.remPairing`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- `⟨R f, ψ⟩` for a test function `ψ` without compact support: the sum over the level-3
lattice cells of the reconstruction of `ψ χ_{3,j}`. -/
def remPairing (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
    (ψ : ParabolicSpace → ℝ) : ℝ :=
  ∑' j : LatticeIndex, M.latticeRecon f (fun y => ψ y * latticeCell 3 j y)

end Model

end RegularityStructures

end
