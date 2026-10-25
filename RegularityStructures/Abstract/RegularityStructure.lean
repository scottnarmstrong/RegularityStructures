/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Regularity structures with a graded basis

A regularity structure `𝒯 = (A, T, G)` [Hai14, Definition 2.1] is recorded through a graded basis:
a finite index type `ι` and degrees `deg : ι → ℝ`. The model space is `T = ι → ℝ`, with basis
vectors `e_i = Pi.single i 1`, and

* `T_α = homogeneousSubspace deg α = span {e_i : deg i = α}`;
* `T_{<α} = lowerSubspace deg α = span {e_i : deg i < α}`.

The index set `A = deg '' univ` is finite, hence bounded below and locally finite. Every
finite-dimensional graded space has a graded basis, so this loses no generality for finite
sectors; the norm `|τ|_α` is replaced by the equivalent coordinatewise bounds. The structure
group is a subgroup `G` of `GL(T)` whose elements are *graded unipotent*:
`Γ τ - τ ∈ T_{<α}` for `τ ∈ T_α` (`isGradedUnipotent_iff`).

Source: [Hai14] = arXiv:1303.5113v4, Definition 2.1; [Hos25] = arXiv:2310.07396v2,
Definition 3.1.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*}

/-- The homogeneous subspace `T_α = span {e_i : deg i = α}`. -/
def homogeneousSubspace (deg : ι → ℝ) (α : ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {τ | ∀ i, deg i ≠ α → τ i = 0}
  add_mem' {τ σ} hτ hσ i hi := by simp [hτ i hi, hσ i hi]
  zero_mem' _ _ := rfl
  smul_mem' c τ hτ i hi := by simp [hτ i hi]

/-- The subspace `T_{<α} = span {e_i : deg i < α}`. -/
def lowerSubspace (deg : ι → ℝ) (α : ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {τ | ∀ i, α ≤ deg i → τ i = 0}
  add_mem' {τ σ} hτ hσ i hi := by simp [hτ i hi, hσ i hi]
  zero_mem' _ _ := rfl
  smul_mem' c τ hτ i hi := by simp [hτ i hi]

/-- A linear map is graded unipotent if `Γ e_i - e_i ∈ T_{<deg i}` for every basis vector. -/
def IsGradedUnipotent [DecidableEq ι] (deg : ι → ℝ) (Γ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop :=
  ∀ i, Γ (Pi.single i 1) - Pi.single i 1 ∈ lowerSubspace deg (deg i)

/-- A regularity structure with graded basis `ι`: degrees `deg i` of the basis vectors and a
structure group `G ≤ GL(ι → ℝ)` of graded unipotent maps [Hai14, Definition 2.1]. -/
structure RegularityStructure (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The homogeneity `|e_i| = deg i` of the basis vector `e_i`. -/
  deg : ι → ℝ
  /-- The structure group. -/
  group : Subgroup (LinearMap.GeneralLinearGroup ℝ (ι → ℝ))
  isGradedUnipotent : ∀ g ∈ group, IsGradedUnipotent deg (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- The finite index set `A_{<γ} = {deg i : deg i < γ}` of homogeneities below `γ`. -/
def RegularityStructure.degreesBelow [Fintype ι] [DecidableEq ι] (𝒯 : RegularityStructure ι) (γ : ℝ) : Finset ℝ :=
  (Finset.univ.filter fun i => 𝒯.deg i < γ).image 𝒯.deg

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι] {deg : ι → ℝ}

omit [DecidableEq ι] in
theorem mem_homogeneousSubspace {α : ℝ} {τ : ι → ℝ} :
    τ ∈ homogeneousSubspace deg α ↔ ∀ i, deg i ≠ α → τ i = 0 :=
  Iff.rfl

omit [DecidableEq ι] in
theorem mem_lowerSubspace {α : ℝ} {τ : ι → ℝ} :
    τ ∈ lowerSubspace deg α ↔ ∀ i, α ≤ deg i → τ i = 0 :=
  Iff.rfl

theorem single_mem_homogeneousSubspace (i : ι) (c : ℝ) :
    Pi.single i c ∈ homogeneousSubspace deg (deg i) := by
  intro j hj
  have : j ≠ i := fun h => hj (h ▸ rfl)
  simp [this]

theorem single_mem_lowerSubspace {i : ι} {α : ℝ} (h : deg i < α) (c : ℝ) :
    Pi.single i c ∈ lowerSubspace deg α := by
  intro j hj
  have : j ≠ i := by rintro rfl; linarith
  simp [this]

omit [DecidableEq ι] in
theorem lowerSubspace_mono {α β : ℝ} (h : α ≤ β) : lowerSubspace deg α ≤ lowerSubspace deg β :=
  fun _ hτ i hi => hτ i (h.trans hi)

/-- `T_{<α}` is the span of the basis vectors of degree `< α`. -/
theorem mem_lowerSubspace_iff_eq_sum [Fintype ι] {α : ℝ} {τ : ι → ℝ} :
    τ ∈ lowerSubspace deg α ↔
      τ = ∑ i ∈ Finset.univ.filter (fun i => deg i < α), Pi.single i (τ i) := by
  constructor
  · intro hτ
    ext j
    rw [Finset.sum_apply]
    by_cases hj : deg j < α
    · rw [Finset.sum_eq_single_of_mem j (by simp [hj])]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
    · rw [hτ j (not_lt.1 hj), Finset.sum_eq_zero]
      intro k hk
      have hk' : k ≠ j := by
        rintro rfl
        exact hj (Finset.mem_filter.1 hk).2
      simp [Ne.symm hk']
  · intro h
    rw [h]
    exact Submodule.sum_mem _ fun i hi => single_mem_lowerSubspace (Finset.mem_filter.1 hi).2 _

theorem eq_sum_single [Fintype ι] (τ : ι → ℝ) : τ = ∑ i, τ i • (Pi.single i 1 : ι → ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

namespace IsGradedUnipotent

variable {Γ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

/-- `Γ e_i` has coordinate `1` at `i`. -/
theorem apply_single_self (hΓ : IsGradedUnipotent deg Γ) (i : ι) : Γ (Pi.single i 1) i = 1 := by
  have h := hΓ i i le_rfl
  simp only [Pi.sub_apply, Pi.single_eq_same] at h
  linarith

/-- The coordinates of `Γ e_i` of degree `≥ deg i`, other than `i` itself, vanish. -/
theorem apply_single_of_le (hΓ : IsGradedUnipotent deg Γ) {i j : ι} (hij : j ≠ i)
    (h : deg i ≤ deg j) : Γ (Pi.single i 1) j = 0 := by
  have h' := hΓ i j h
  simpa [Pi.single_apply, hij] using h'

/-- Graded unipotent maps preserve `T_{<α}`. -/
theorem map_lowerSubspace [Fintype ι] (hΓ : IsGradedUnipotent deg Γ) {α : ℝ} {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace deg α) : Γ τ ∈ lowerSubspace deg α := by
  rw [mem_lowerSubspace_iff_eq_sum.1 hτ, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi : deg i < α := (Finset.mem_filter.1 hi).2
  have hsingle : (Pi.single i (τ i) : ι → ℝ) = τ i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hsingle, map_smul]
  refine Submodule.smul_mem _ _ ?_
  have h1 : Γ (Pi.single i 1) = (Γ (Pi.single i 1) - Pi.single i 1) + Pi.single i 1 := by abel
  rw [h1]
  exact Submodule.add_mem _ (lowerSubspace_mono hi.le (hΓ i)) (single_mem_lowerSubspace hi 1)

end IsGradedUnipotent

theorem isGradedUnipotent_id : IsGradedUnipotent deg (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :=
  fun _ => by simp

theorem IsGradedUnipotent.comp [Fintype ι] {Γ Γ' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hΓ : IsGradedUnipotent deg Γ)
    (hΓ' : IsGradedUnipotent deg Γ') : IsGradedUnipotent deg (Γ ∘ₗ Γ') := by
  intro i
  have h : (Γ ∘ₗ Γ') (Pi.single i 1) - Pi.single i 1 =
      Γ (Γ' (Pi.single i 1) - Pi.single i 1) + (Γ (Pi.single i 1) - Pi.single i 1) := by
    simp [map_sub]
  rw [h]
  exact Submodule.add_mem _ (hΓ.map_lowerSubspace (hΓ' i)) (hΓ i)

/-- A graded unipotent map has a graded unipotent inverse. -/
theorem IsGradedUnipotent.inv [Fintype ι] {g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)}
    (hg : IsGradedUnipotent deg (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) :
    IsGradedUnipotent deg ((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) :
      (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := by
  have hinv : ∀ w, ((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) w) = w := fun w => by
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  -- `g⁻¹` preserves `T_{<α}`: `g` restricts to an injective, hence surjective, endomorphism.
  have hpres : ∀ α, ∀ v ∈ lowerSubspace deg α,
      ((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) v ∈
        lowerSubspace deg α := by
    intro α v hv
    set gr := (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)).restrict
      (p := lowerSubspace deg α) (q := lowerSubspace deg α) fun w hw => hg.map_lowerSubspace hw
    have hinj : Function.Injective gr := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simp only [gr, LinearMap.coe_restrict_apply] at this
      rw [← hinv a, ← hinv b, this]
    obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨v, hv⟩
    have hw' : (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) w = v := by
      have := congrArg Subtype.val hw
      simpa [gr] using this
    rw [← hw', hinv]
    exact w.2
  intro i
  have h : ((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      (Pi.single i 1) - Pi.single i 1 =
      -((g⁻¹ : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
        ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single i 1) - Pi.single i 1) := by
    rw [map_sub, hinv]
    abel
  rw [h]
  exact Submodule.neg_mem _ (hpres _ _ (hg i))

namespace RegularityStructure

variable [Fintype ι] (𝒯 : RegularityStructure ι)

theorem mem_degreesBelow {γ a : ℝ} : a ∈ 𝒯.degreesBelow γ ↔ ∃ i, 𝒯.deg i < γ ∧ 𝒯.deg i = a := by
  simp [degreesBelow]

end RegularityStructure

end RegularityStructures

end
