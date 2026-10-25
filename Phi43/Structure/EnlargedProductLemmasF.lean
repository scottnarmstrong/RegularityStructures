/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedProductF
public import Phi43.Structure.EnlargedDegreesF
import Mathlib.Tactic.Linarith

/-!
# Evaluation and unit laws for the enlarged product

Hairer [Hai14, Definition 4.1]. The retained table agrees literally with
the product on basis vectors and has the old constant symbol as a genuine
two-sided unit, including on the new planted symbols.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43ProductLinearF_basis (τ σ : SymbolF) :
    phi43ProductLinearF (Pi.single τ 1) (Pi.single σ 1) = phi43ProductBasisF τ σ := by
  simp [phi43ProductLinearF, Pi.single_apply]

theorem phi43ProductLinearF_old_basis (τ σ : Symbol) :
    phi43ProductLinearF (Pi.single (.old τ) 1) (Pi.single (.old σ) 1) =
      phi43OldEmbF (phi43CoordinateEquiv (basis τ * basis σ)) := by
  rw [phi43ProductLinearF_basis, multiply_basis]
  unfold phi43ProductBasisF basisProduct
  cases h : productSymbol τ σ with
  | none => simp [phi43ProductSymbolF, h]
  | some υ =>
    simp [phi43ProductSymbolF, h, phi43CoordinateEquiv_basis, phi43OldEmbF_single]

end RegularityStructures.Phi43

end
