/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Realising.Germ
public import RegularityStructures.Abstract.ModelLocal
public import RegularityStructures.Analysis.Heat.Schauder.TaylorDyadicSum
public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Annihilating.KernelSupport

/-!
# The density of `Π_x I e_i`

`realGerm`: `y ↦ ∑_n ⟨Π_x e_i, K^{deg i}_{n;xy}⟩` with `K_n = annShell N n`, the density of
`Π_x I e_i` with respect to Lebesgue measure; `degreesBelowLe_bounds_two` transfers the degree bound
`> -2` to the degrees `a ≤ deg i`.

Source: [Hai14, Remark 5.10].
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- `y ↦ ∑_n ⟨Π_x e_i, K^{deg i}_{n;xy}⟩` with `K_n = annShell N n`: the density of
`Π_x I e_i` against Lebesgue measure in Hairer's Remark 5.10. -/
def realGerm (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (x : ParabolicSpace) (i : ι)
    (y : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing (fun t z => M.regPi x (Pi.single i 1) t z)
    (taylorKernel (annKernel0 N) n (𝒯.deg i + 2) x y)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The degrees `a ≤ deg i` among those below `γ` are `> -2` if all degrees below `γ` are. -/
theorem degreesBelowLe_bounds_two {γ : ℝ} (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j) (i : ι) :
    ∀ a ∈ 𝒯.degreesBelowLe γ (𝒯.deg i), -2 < a ∧ a ≤ 𝒯.deg i := by
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
  obtain ⟨j, hj, rfl⟩ := 𝒯.mem_degreesBelow.1 ha1
  exact ⟨hdeg j hj, ha2⟩

end RegularityStructures

end
