/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration

/-!
# Sector-restricted exponent sets and local orders

For a sector `V` spanned by basis vectors (`𝒯.IsSector V` and `basis_mem`), the vectors
`Γ_{yx} e_i` with `e_i ∈ V` and the increments `f(y) − Γ_{yx} f(x)` of a modelled distribution
with values in `V` only have components along the basis vectors `e_j ∈ V`. Hence the local
orders of `Π_x e_i` and of `Rf − Π_x f(x)`, and the coherence of the germ `Π_y f(y)`, hold with
exponents taken among the degrees of the basis vectors of `V` only
(`RegularityStructure.degreesBelowIn`). This is what allows the multilevel Schauder estimate
to be applied to a sector `V` of degrees `> -2` inside a structure that also contains basis
vectors of degree `≤ -2` outside `V` (e.g. the noise symbol of Φ⁴₃).

Sources: [Hai14] = arXiv:1303.5113v4, (2.15), Theorem 3.10; [Hos25] = arXiv:2310.07396v2,
Remark 3.4 and §4, step (1).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RegularityStructure

open scoped Classical in
/-- The basis indices `j` with `e_j ∈ V` and `deg j < γ`. -/
def sectorBelow (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) (γ : ℝ) : Finset ι :=
  Finset.univ.filter fun j => (Pi.single j 1 : ι → ℝ) ∈ V ∧ 𝒯.deg j < γ

/-- The homogeneities `< γ` of basis vectors lying in `V`. -/
def degreesBelowIn (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) (γ : ℝ) : Finset ℝ :=
  (𝒯.sectorBelow V γ).image 𝒯.deg

/-- The homogeneities `a ≤ α`, `a < γ` of basis vectors lying in `V`. -/
def degreesBelowLeIn (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) (γ α : ℝ) :
    Finset ℝ :=
  (𝒯.degreesBelowIn V γ).filter (· ≤ α)

variable (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ))

theorem mem_sectorBelow {γ : ℝ} {j : ι} :
    j ∈ 𝒯.sectorBelow V γ ↔ (Pi.single j 1 : ι → ℝ) ∈ V ∧ 𝒯.deg j < γ := by
  simp [sectorBelow]

theorem mem_degreesBelowIn {γ a : ℝ} :
    a ∈ 𝒯.degreesBelowIn V γ ↔ ∃ j, (Pi.single j 1 : ι → ℝ) ∈ V ∧ 𝒯.deg j < γ ∧ 𝒯.deg j = a := by
  unfold degreesBelowIn
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, ((𝒯.mem_sectorBelow V).1 hj).1, ((𝒯.mem_sectorBelow V).1 hj).2, rfl⟩
  · rintro ⟨j, hV, hj, rfl⟩
    exact ⟨j, (𝒯.mem_sectorBelow V).2 ⟨hV, hj⟩, rfl⟩

theorem degreesBelowIn_subset {γ : ℝ} : 𝒯.degreesBelowIn V γ ⊆ 𝒯.degreesBelow γ := by
  intro a ha
  obtain ⟨j, -, hj, rfl⟩ := (𝒯.mem_degreesBelowIn V).1 ha
  exact (𝒯.mem_degreesBelow).2 ⟨j, hj, rfl⟩

end RegularityStructure

/-- A sum over the basis vectors of `V` of degree `< γ` of a function of the degree is at most
`|ι|` times the sum over the set of degrees. -/
theorem sum_sectorBelow_le_card_mul (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ))
    (γ : ℝ) {h : ℝ → ℝ} (hh : ∀ a ∈ 𝒯.degreesBelowIn V γ, 0 ≤ h a) :
    ∑ j ∈ 𝒯.sectorBelow V γ, h (𝒯.deg j) ≤
      Fintype.card ι * ∑ a ∈ 𝒯.degreesBelowIn V γ, h a := by
  have hS : 0 ≤ ∑ a ∈ 𝒯.degreesBelowIn V γ, h a := Finset.sum_nonneg hh
  calc ∑ j ∈ 𝒯.sectorBelow V γ, h (𝒯.deg j)
      ≤ ∑ _j ∈ 𝒯.sectorBelow V γ, ∑ a ∈ 𝒯.degreesBelowIn V γ, h a := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hmem : 𝒯.deg j ∈ 𝒯.degreesBelowIn V γ := Finset.mem_image_of_mem _ hj
        exact Finset.single_le_sum hh hmem
    _ = (𝒯.sectorBelow V γ).card * ∑ a ∈ 𝒯.degreesBelowIn V γ, h a := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * ∑ a ∈ 𝒯.degreesBelowIn V γ, h a := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        exact_mod_cast Finset.card_le_univ _

end RegularityStructures

end
