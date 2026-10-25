/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Slab.BlockProj
public import RegularityStructures.Abstract.Model

/-!
# The block projection on slab spaces

`SlabSpace.blockProjMap` is the linear map `D^{γ,η}_P(V) → D^{γ,η}_P(V')` induced by `RegularityStructures.blockProj A`
(block invariance of the structure group, and `RegularityStructures.blockProj A` maps `V` into `V'`);
`SlabSpace.blockProj` is the case `V = V' = ⊤`. Both are norm-nonincreasing.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V V' : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

/-- Block projection preserves membership in `slabModelledDistributions` (for `V → V'`). -/
theorem blockProj_mem_slabModelledDistributions {A : Finset ι}
    (hA : ∀ x y τ, M.gammaMap x y (RegularityStructures.blockProj A τ) = RegularityStructures.blockProj A (M.gammaMap x y τ))
    (hV : ∀ τ ∈ V, RegularityStructures.blockProj A τ ∈ V') {f : E → ι → ℝ}
    (hf : f ∈ M.slabModelledDistributions ρ V γ η S) :
    (fun x => RegularityStructures.blockProj A (f x)) ∈ M.slabModelledDistributions ρ V' γ η S := by
  obtain ⟨hm, hV0, h0, C, hC⟩ := hf
  refine ⟨(measurable_blockProj A).comp hm, fun x hx hρ => ?_, fun x hx => ?_, C,
    hC.blockProj M hA⟩
  · obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hV0 x hx hρ)
    exact Submodule.mem_inf.2 ⟨hV _ h1, blockProj_mem_lowerSubspace A h2⟩
  · simp [h0 x hx]

end Model

end RegularityStructures

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V V' : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

/-- The block projection `D^{γ,η}_P(V) → D^{γ,η}_P(V')` on the slab space. -/
def SlabSpace.blockProjMap (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (RegularityStructures.blockProj A τ) = RegularityStructures.blockProj A (M.gammaMap x y τ))
    (hV : ∀ τ ∈ V, RegularityStructures.blockProj A τ ∈ V') :
    M.SlabSpace ρ V γ η S →ₗ[ℝ] M.SlabSpace ρ V' γ η S where
  toFun u := SlabSpace.mk (fun x => RegularityStructures.blockProj A (u.val x))
    (blockProj_mem_slabModelledDistributions hA hV u.val_mem)
  map_add' u v := by
    ext x
    simp [map_add]
  map_smul' c u := by
    ext x
    simp [map_smul]

/-- The block projection on `D^{γ,η}_P` (no sector constraint). -/
def SlabSpace.blockProj (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (RegularityStructures.blockProj A τ) =
      RegularityStructures.blockProj A (M.gammaMap x y τ)) :
    M.SlabSpace ρ (⊤ : Submodule ℝ (ι → ℝ)) γ η S →ₗ[ℝ]
      M.SlabSpace ρ (⊤ : Submodule ℝ (ι → ℝ)) γ η S :=
  SlabSpace.blockProjMap A hA fun _ _ => Submodule.mem_top

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V V' : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

theorem SlabSpace.norm_blockProjMap_le (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (RegularityStructures.blockProj A τ) = RegularityStructures.blockProj A (M.gammaMap x y τ))
    (hV : ∀ τ ∈ V, RegularityStructures.blockProj A τ ∈ V') (u : M.SlabSpace ρ V γ η S) :
    ‖SlabSpace.blockProjMap A hA hV u‖ ≤ ‖u‖ :=
  SlabSpace.norm_le _ (norm_nonneg u) (u.singularBoundOn_norm.blockProj M hA)

theorem SlabSpace.val_blockProj (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (RegularityStructures.blockProj A τ) =
      RegularityStructures.blockProj A (M.gammaMap x y τ))
    (u : M.SlabSpace ρ (⊤ : Submodule ℝ (ι → ℝ)) γ η S) :
    (SlabSpace.blockProj A hA u).val = fun x => RegularityStructures.blockProj A (u.val x) :=
  rfl

theorem SlabSpace.norm_blockProj_le (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (RegularityStructures.blockProj A τ) =
      RegularityStructures.blockProj A (M.gammaMap x y τ))
    (u : M.SlabSpace ρ (⊤ : Submodule ℝ (ι → ℝ)) γ η S) :
    ‖SlabSpace.blockProj A hA u‖ ≤ ‖u‖ :=
  SlabSpace.norm_blockProjMap_le A hA _ u

end Model

end RegularityStructures

end
