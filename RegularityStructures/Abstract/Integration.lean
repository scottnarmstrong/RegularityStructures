/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.RegularityStructure
public import RegularityStructures.Abstract.Polynomial

/-!
# Sectors, abstract polynomials and abstract integration maps

The algebraic layer of [Hai14, §5] in the graded-basis representation:

* `homogeneousProj deg α`: the projection `Q_α : T → T_α`;
* `RegularityStructure.IsSector V`: `V` is graded (`Q_α V ⊂ V` for all `α`) and `G`-invariant
  [Hai14, Definition 2.5] (complements exist automatically in finite dimension); the regularity
  condition `V_β = 0` for `β < α` is `IsSector.OfRegularity`;
* `PolynomialSector 𝒯 N`: an embedding of the abstract polynomials `X^k`, `|k|_𝔰 < N`, into the
  basis of `𝒯`, preserving degrees, whose span `T̄` is `G`-invariant [Hai14, §5, before
  Assumption 5.3];
* `IsAbstractIntegration P V I β`: `I : T → T` is an abstract integration map of order `β` on the
  sector `V` [Hai14, Definition 5.7]: `I (V ∩ T_α) ⊂ T_{α+β}`, `I = 0` on `V ∩ T̄`, and
  `IΓa − ΓIa ∈ T̄` for `a ∈ V`, `Γ ∈ G`.

Source: [Hai14] = arXiv:1303.5113v4, Definitions 2.5 and 5.7.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*}

/-- The projection `Q_α : T → T_α` onto the homogeneous component of degree `α`. -/
def homogeneousProj (deg : ι → ℝ) (α : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun τ i := if deg i = α then τ i else 0
  map_add' τ σ := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c τ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

variable [Fintype ι] [DecidableEq ι]

namespace RegularityStructure

/-- A sector [Hai14, Definition 2.5]: a graded, `G`-invariant subspace of `T`. -/
structure IsSector (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) : Prop where
  graded : ∀ α, ∀ a ∈ V, homogeneousProj 𝒯.deg α a ∈ V
  invariant : ∀ g ∈ 𝒯.group, ∀ a ∈ V,
    ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) a ∈ V

/-- A sector of regularity `α`: `V_β = {0}` for `β < α`. -/
def IsSector.OfRegularity (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) (α : ℝ) :
    Prop :=
  ∀ β < α, ∀ a ∈ V, homogeneousProj 𝒯.deg β a = 0

end RegularityStructure

/-- The abstract polynomials `X^k`, `|k|_𝔰 < N`, inside a regularity structure on `ℝ⁴`: an
injective, degree-preserving embedding of `PolyIndex N` into the basis whose span `T̄` is
invariant under the structure group. -/
structure PolynomialSector (𝒯 : RegularityStructure ι) (N : ℕ) where
  /-- The basis index of `X^k`. -/
  emb : PolyIndex N → ι
  emb_injective : Function.Injective emb
  deg_emb : ∀ k, 𝒯.deg (emb k) = polyDeg N k
  invariant : ∀ g ∈ 𝒯.group, ∀ τ : ι → ℝ, (∀ i, i ∉ Set.range emb → τ i = 0) →
    ∀ i, i ∉ Set.range emb →
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) τ i = 0

namespace PolynomialSector

variable {𝒯 : RegularityStructure ι} {N : ℕ}

/-- The span `T̄` of the abstract polynomials. -/
def subspace (P : PolynomialSector 𝒯 N) : Submodule ℝ (ι → ℝ) where
  carrier := {τ | ∀ i, i ∉ Set.range P.emb → τ i = 0}
  add_mem' {τ σ} hτ hσ i hi := by simp [hτ i hi, hσ i hi]
  zero_mem' _ _ := rfl
  smul_mem' c τ hτ i hi := by simp [hτ i hi]

end PolynomialSector

/-- An abstract integration map of order `β` on the sector `V` [Hai14, Definition 5.7]. -/
structure IsAbstractIntegration {𝒯 : RegularityStructure ι} {N : ℕ}
    (P : PolynomialSector 𝒯 N) (V : Submodule ℝ (ι → ℝ)) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (β : ℝ) : Prop where
  pos : 0 < β
  map_homogeneous : ∀ α, ∀ a ∈ V, a ∈ homogeneousSubspace 𝒯.deg α →
    I a ∈ homogeneousSubspace 𝒯.deg (α + β)
  map_poly : ∀ a ∈ V, a ∈ P.subspace → I a = 0
  comm : ∀ g ∈ 𝒯.group, ∀ a ∈ V,
    I (((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) a) -
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (I a) ∈ P.subspace

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneousProj_apply (deg : ι → ℝ) (α : ℝ) (τ : ι → ℝ) (i : ι) :
    homogeneousProj deg α τ i = if deg i = α then τ i else 0 :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneousProj_mem (deg : ι → ℝ) (α : ℝ) (τ : ι → ℝ) :
    homogeneousProj deg α τ ∈ homogeneousSubspace deg α := by
  intro i hi
  simp [homogeneousProj_apply, hi]

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneousProj_eq_self {deg : ι → ℝ} {α : ℝ} {τ : ι → ℝ}
    (hτ : τ ∈ homogeneousSubspace deg α) : homogeneousProj deg α τ = τ := by
  funext i
  rw [homogeneousProj_apply]
  split_ifs with h
  · rfl
  · exact (hτ i h).symm

omit [DecidableEq ι] in
/-- `τ = ∑_{α ∈ deg(ι)} Q_α τ`: the decomposition `T = ⊕_α T_α`. -/
theorem sum_homogeneousProj (deg : ι → ℝ) (τ : ι → ℝ) :
    ∑ α ∈ Finset.univ.image deg, homogeneousProj deg α τ = τ := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single_of_mem (deg i) (Finset.mem_image_of_mem _
    (Finset.mem_univ i))]
  · simp [homogeneousProj_apply]
  · intro α _ hα
    simp [homogeneousProj_apply, Ne.symm hα]

end RegularityStructures

end
