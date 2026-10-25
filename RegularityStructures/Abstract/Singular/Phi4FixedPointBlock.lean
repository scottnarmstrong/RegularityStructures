/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Slab.BlockOperator
public import RegularityStructures.Abstract.Singular.Layer.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.Slab.OperatorSlab

/-!
# Block sector and layer setting for block-projected slab elements

Preparatory lemmas for the unconditional `Φ⁴₃` fixed point (Hairer, arXiv:1303.5113v4,
Theorem 7.1 and Theorem 7.8):

* `blockSpan A`, the span of the basis vectors `e_i`, `i ∈ A` (the sector on which the integration
  operator `I` acts), and its coordinate characterisation;
* `Model.SingularBoundOn.indicator_self`: a bound on `S` passes to `S.indicator f`;
* `Model.layerSetting_blockProj`: for a slab element `g ∈ D^{γ̄,η''}_P(⊤)` on `(0, T] × ℝ³` and
  `A` a block with `ζ ≤ deg i` for `i ∈ A`, the function `(blockProj A g).val` satisfies the
  `LayerSetting` hypotheses of Hairer's Proposition 6.16 with constant `‖blockProj A g‖`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι]

/-- The block sector `V_A = span {e_i : i ∈ A}`. -/
def blockSpan (A : Finset ι) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ ((fun i => (Pi.single i 1 : ι → ℝ)) '' (A : Set ι))

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι]

theorem blockProj_eq_self_of_mem_blockSpan {A : Finset ι} {τ : ι → ℝ} (hτ : τ ∈ blockSpan A) :
    blockProj A τ = τ := by
  refine blockProj_eq_self_of_mem_span ?_
  have : (fun i => (Pi.single i 1 : ι → ℝ)) '' (A : Set ι) =
      {e : ι → ℝ | ∃ i ∈ A, e = Pi.single i 1} := by
    ext e
    simp [eq_comm]
  rwa [blockSpan, this] at hτ

theorem eq_zero_of_notMem_of_mem_blockSpan {A : Finset ι} {τ : ι → ℝ} (hτ : τ ∈ blockSpan A)
    {i : ι} (hi : i ∉ A) : τ i = 0 := by
  rw [← blockProj_eq_self_of_mem_blockSpan hτ, blockProj_apply_of_notMem hi]

theorem mem_blockSpan_of_forall [Fintype ι] {A : Finset ι} {τ : ι → ℝ}
    (h : ∀ i, i ∉ A → τ i = 0) : τ ∈ blockSpan A := by
  have hτ : τ = ∑ i ∈ A, τ i • (Pi.single i 1 : ι → ℝ) := by
    funext j
    by_cases hj : j ∈ A
    · simp [Finset.sum_apply, Pi.single_apply, hj]
    · simp [Finset.sum_apply, Pi.single_apply, h j hj]
  rw [hτ]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem mem_of_single_mem_blockSpan {A : Finset ι} {i : ι}
    (h : (Pi.single i 1 : ι → ℝ) ∈ blockSpan A) : i ∈ A := by
  by_contra hi
  have := eq_zero_of_notMem_of_mem_blockSpan h hi
  simp at this

theorem isCoordClosed_blockSpan [Fintype ι] (A : Finset ι) : IsCoordClosed (blockSpan A) := by
  intro a ha j hj
  refine Submodule.subset_span ⟨j, ?_, rfl⟩
  by_contra hjA
  exact hj (eq_zero_of_notMem_of_mem_blockSpan ha hjA)

variable [Fintype ι] {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}

/-- A singular bound on `S` passes to `S.indicator f`. -/
theorem SingularBoundOn.indicator_self {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : M.SingularBoundOn ρ γ η C S f) : M.SingularBoundOn ρ γ η C S (S.indicator f) := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · simpa [Set.indicator_of_mem hx] using h.1 x hx hρ i hi
  · simpa [Set.indicator_of_mem hx, Set.indicator_of_mem hy] using h.2 x hx y hy hρx hρy hd j hj

end Model

end RegularityStructures

end

