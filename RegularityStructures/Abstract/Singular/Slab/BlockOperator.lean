/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Slab.BlockProjMap
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Model

/-!
# The operator `g ↦ Q_{<γ₀} F (blockProj A g)` on the time slab

Packaging of the block projection and `slabOfOperator`: for `F` a map on functions that is additive
and homogeneous on block-projected slab elements and satisfies the singular bounds on slab
elements `u` with constant `C ‖u‖`, `slabOfBlockOperator` is the linear map
`g ↦ Q_{<γ₀} F ((blockProj A g).val)` into `D^{γ₀,η₀}_P(V)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ParabolicSpace}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup ParabolicSpace μ}
  {M : Model 𝒯 K} {T : ℝ} {γb η'' : ℝ}

/-- The linear map `g ↦ F ((blockProj A g).val)` from `D^{γ̄,η''}_P` to functions. -/
def blockOperator (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (blockProj A τ) = blockProj A (M.gammaMap x y τ))
    (F : (ParabolicSpace → ι → ℝ) → ParabolicSpace → ι → ℝ)
    (hFadd : ∀ g h : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T),
      F (SlabSpace.blockProj A hA (g + h)).val =
        F (SlabSpace.blockProj A hA g).val + F (SlabSpace.blockProj A hA h).val)
    (hFsmul : ∀ (c : ℝ) (g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T)),
      F (SlabSpace.blockProj A hA (c • g)).val = c • F (SlabSpace.blockProj A hA g).val) :
    M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T) →ₗ[ℝ] (ParabolicSpace → ι → ℝ) where
  toFun g := F (SlabSpace.blockProj A hA g).val
  map_add' := hFadd
  map_smul' := hFsmul

end Model

end RegularityStructures

end

