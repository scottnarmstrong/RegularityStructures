/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointSlabSpace
public import RegularityStructures.Abstract.Model

/-!
# Block projections on the model space and on slab spaces

For `A : Finset ι` the coordinate projection `blockProj A` keeps the coordinates in `A`. When the
structure group commutes with it (`hA`, block invariance; for `Φ⁴₃` with `A` all symbols except `Ξ`),
it preserves `D^{γ,η}_P` bounds with the same constant, hence induces a norm-nonincreasing linear
map of the slab spaces.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate projection onto the block `A`: `(blockProj A τ) i = if i ∈ A then τ i else 0`. -/
def blockProj (A : Finset ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun τ i := if i ∈ A then τ i else 0
  map_add' τ σ := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c τ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι]

theorem blockProj_apply (A : Finset ι) (τ : ι → ℝ) (i : ι) :
    blockProj A τ i = if i ∈ A then τ i else 0 :=
  rfl

theorem blockProj_apply_of_mem {A : Finset ι} {i : ι} (h : i ∈ A) (τ : ι → ℝ) :
    blockProj A τ i = τ i := by
  simp [blockProj_apply, h]

theorem blockProj_apply_of_notMem {A : Finset ι} {i : ι} (h : i ∉ A) (τ : ι → ℝ) :
    blockProj A τ i = 0 := by
  simp [blockProj_apply, h]

theorem abs_blockProj_apply_le (A : Finset ι) (τ : ι → ℝ) (i : ι) :
    |blockProj A τ i| ≤ |τ i| := by
  rw [blockProj_apply]
  split_ifs <;> simp

theorem blockProj_eq_self_iff {A : Finset ι} {τ : ι → ℝ} :
    blockProj A τ = τ ↔ ∀ i, i ∉ A → τ i = 0 := by
  constructor
  · intro h i hi
    rw [← h, blockProj_apply_of_notMem hi]
  · intro h
    funext i
    by_cases hi : i ∈ A
    · exact blockProj_apply_of_mem hi τ
    · rw [blockProj_apply_of_notMem hi, h i hi]

theorem blockProj_eq_self_of_mem_span {A : Finset ι} {τ : ι → ℝ}
    (hτ : τ ∈ Submodule.span ℝ {e : ι → ℝ | ∃ i ∈ A, e = Pi.single i 1}) :
    blockProj A τ = τ := by
  induction hτ using Submodule.span_induction with
  | mem e he =>
    obtain ⟨i, hi, rfl⟩ := he
    refine blockProj_eq_self_iff.2 fun j hj => ?_
    have : j ≠ i := fun h => hj (h ▸ hi)
    simp [this]
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, ha]

theorem measurable_blockProj [Finite ι] (A : Finset ι) :
    Measurable (blockProj A : (ι → ℝ) → ι → ℝ) :=
  (blockProj A).continuous_of_finiteDimensional.measurable

variable [Fintype ι]

theorem blockProj_mem_lowerSubspace {𝒯 : RegularityStructure ι} (A : Finset ι)
    {γ : ℝ} {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ) :
    blockProj A τ ∈ lowerSubspace 𝒯.deg γ := by
  intro i hi
  rw [blockProj_apply, hτ i hi]
  simp

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- **Block projection preserves the singular bounds** (same constant), when the structure group
commutes with `blockProj A`. -/
theorem SingularBoundOn.blockProj {A : Finset ι}
    (hA : ∀ x y τ, M.gammaMap x y (RegularityStructures.blockProj A τ) =
      RegularityStructures.blockProj A (M.gammaMap x y τ))
    {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {f : E → ι → ℝ}
    (hf : M.SingularBoundOn ρ γ η C S f) :
    M.SingularBoundOn ρ γ η C S (fun x => RegularityStructures.blockProj A (f x)) := by
  have hw : ∀ (a b : ℝ), 0 ≤ b → |a| ≤ C * b → ∀ s : ℝ, |s| ≤ |a| → |s| ≤ C * b :=
    fun _ _ _ h _ hs => hs.trans h
  refine ⟨fun x hx hρ i hi => hw _ _ ?_ (hf.1 x hx hρ i hi) _ (abs_blockProj_apply_le A _ i),
    fun x hx y hy hρx hρy hd j hj => ?_⟩
  · exact Real.rpow_nonneg (singularWeight_pos hρ).le _
  · have h := hf.2 x hx y hy hρx hρy hd j hj
    have e : (RegularityStructures.blockProj A (f y) -
        M.gammaMap y x (RegularityStructures.blockProj A (f x))) =
        RegularityStructures.blockProj A (f y - M.gammaMap y x (f x)) := by
      rw [hA, map_sub]
    rw [e]
    exact (abs_blockProj_apply_le A _ j).trans h

end Model

end RegularityStructures

end
