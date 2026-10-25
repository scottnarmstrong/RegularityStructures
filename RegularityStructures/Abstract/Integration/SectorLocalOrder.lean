/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SectorLocal
public import RegularityStructures.Abstract.Model

/-!
# Local order of `Π_x e_i` with exponents from the sector

Sector-restricted version of `Model.isLocalOrder_regPi_single` ([Hos25, Remark 3.4, (3.1)],
[Hai14, (2.15)]): for `e_i ∈ V`, `V` a sector spanned by basis vectors, `Π_x e_i` is of local
order `deg i` at `x` with the exponent set `degreesBelowLeIn V γ (deg i)`, which only involves
the degrees of basis vectors of `V` (`Γ_{yx} e_i` has no other components).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)
  {V : Submodule ℝ (ι → ℝ)}

/-- For `τ ∈ V ∩ T_{<γ}`, `(Q_t Π_x τ)(z) = ∑_{e_j ∈ V, deg j < γ} τ_j (Q_t Π_x e_j)(z)`. -/
theorem regPi_eq_sum_sectorBelow
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) {γ : ℝ} {τ : ι → ℝ}
    (hτV : τ ∈ V) (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (x : E) (t : ℝ) (z : E) :
    M.regPi x τ t z =
      ∑ j ∈ 𝒯.sectorBelow V γ, τ j * M.regPi x (Pi.single j 1) t z := by
  rw [M.regPi_eq_sum, ← Finset.sum_subset (Finset.subset_univ (𝒯.sectorBelow V γ))]
  intro j _ hj
  by_cases h0 : τ j = 0
  · rw [h0, zero_mul]
  · exact absurd ((𝒯.mem_sectorBelow V).2 ⟨hVb τ hτV j h0, by
      by_contra hlt
      exact h0 (hτ j (not_lt.1 hlt))⟩) hj

end Model

end RegularityStructures

end
