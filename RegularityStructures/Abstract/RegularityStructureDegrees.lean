/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.RegularityStructure
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Degrees below a level

`RegularityStructure.lt_of_mem_degreesBelow`: every element of `𝒯.degreesBelow γ` is `< γ`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*}

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι] {deg : ι → ℝ}

namespace IsGradedUnipotent

variable {Γ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

end IsGradedUnipotent

namespace RegularityStructure

variable [Fintype ι] (𝒯 : RegularityStructure ι)

theorem lt_of_mem_degreesBelow {γ a : ℝ} (ha : a ∈ 𝒯.degreesBelow γ) : a < γ := by
  obtain ⟨i, hi, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
  exact hi

end RegularityStructure

end RegularityStructures

end
