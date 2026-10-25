/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.ExcludedKappa
public import Phi43.Constants
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Phi43.Structure.Symbols

/-!
# Parameter arithmetic for the Theorem A assembly

The parameter choice is internal to the proof of Theorem A.  It avoids the finite excluded set
`excludedKappa` of the stopped continuity of classical solutions and of the convergence of the
G-models, while retaining `κ < -1/2 - η`.  The counterterm identity records the shift
`c = (a / 3, 0)` used in the convergence of the G-models.
-/

public section

open Set

namespace RegularityStructures.Phi43

private theorem assembly_excludedKappa_countable :
    Set.Countable Statements.excludedKappa := by
  refine (Set.countable_range
    (fun p : ℕ × ℕ × ℤ => ((p.2.2 : ℝ) / 2 - (p.2.1 : ℝ)) / (p.1 : ℝ))).mono ?_
  rintro q ⟨⟨b, -, n, -, m, rfl⟩, -⟩
  exact ⟨(b, n, m), rfl⟩

theorem assembly_exists_kappa (η : ℝ) (hη : η < -(1 / 2 : ℝ)) :
    ∃ κ : Kappa,
      κ.1 ∉ Statements.excludedKappa ∧ κ.1 < -(1 / 2 : ℝ) - η := by
  have hlt : (0 : ℝ) < min (1 / 16) (-(1 / 2 : ℝ) - η) :=
    lt_min (by norm_num) (by linarith)
  obtain ⟨k, hk, hk0, hk1⟩ :=
    (assembly_excludedKappa_countable.dense_compl ℝ).exists_between hlt
  exact ⟨⟨k, hk0, lt_of_lt_of_le hk1 (min_le_left _ _)⟩, hk,
    lt_of_lt_of_le hk1 (min_le_right _ _)⟩

end RegularityStructures.Phi43

end
