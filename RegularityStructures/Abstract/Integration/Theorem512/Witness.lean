/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Bounds
public import RegularityStructures.Abstract.Integration
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# The identity polynomial sector

`polySector N'` is the identity polynomial sector of the polynomial regularity structure
`polynomialStructure N'`.

The hypotheses `SchauderSetting` and `SchauderNonIntegral` of the multilevel Schauder theorems
(`kGamma_mem_modelledDistributions`, `reconstruct_kGamma`) are jointly satisfiable with a nonzero
sector: the witness `SchauderWitness.schauderSetting_witness` of the `Witnesses` test library takes
the basis `{X^k} ⊔ {Ξ, IΞ}` with `|Ξ| = -1/2`, `|IΞ| = 3/2`, the polynomial model on `X^k` with
`Π_x Ξ = Π_x IΞ = 0`, the sector `V = ℝ Ξ`, `I Ξ = IΞ` and `γ = 7/4`.
-/

public section

open Set

namespace RegularityStructures

/-- The identity polynomial sector of the polynomial regularity structure. -/
@[expose] def polySector (N' : ℕ) : PolynomialSector (polynomialStructure N') N' where
  emb := id
  emb_injective := Function.injective_id
  deg_emb _ := rfl
  invariant _ _ _ _ i hi := absurd ⟨i, rfl⟩ hi

end RegularityStructures

end
