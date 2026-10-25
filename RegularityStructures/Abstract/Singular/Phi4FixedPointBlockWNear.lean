/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.Slab.BlockProjMap
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Window layer setting for block-projected slab elements, near-pair `Γ`-bounds

When `Γ` commutes with the projection onto the block `A`, the block projection of a slab element `g`
satisfies the window layer setting `LayerSettingWNear`, with constant its norm, for models whose
`Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- **Window layer setting for block-projected slab elements.** -/
theorem layerSettingW_blockProj_near {M : Model 𝒯 parabolicSemigroup}
    {γb η'' ζ CPi CGam T : ℝ} (A : Finset ι)
    (hA : ∀ x y τ, M.gammaMap x y (blockProj A τ) = blockProj A (M.gammaMap x y τ))
    (g : M.SlabSpace timeZeroDist ⊤ γb η'' (timeSlab T)) (hγb : 0 < γb)
    (hPi : M.PiBoundOn γb CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γb CGam hairerTimeWindow)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γb C' C'' ρP ρG p q) (hT : T ≤ 1)
    (hdeg : ∀ j, 𝒯.deg j < γb → -4 < 𝒯.deg j) (hAζ : ∀ i ∈ A, ζ ≤ 𝒯.deg i) (hζγ : ζ ≤ γb)
    (hζη : -2 < min ζ η'') :
    LayerSettingWNear M (SlabSpace.blockProj A hA g).val γb η'' ζ ‖SlabSpace.blockProj A hA g‖
      CPi CGam T where
  hγ := hγb
  hPi := hPi
  hCPi := hCPi
  hGam := hGam
  hgrowth := hgrowth
  hT := hT
  hdeg := hdeg
  hfT z := by
    by_cases hz : z ∈ timeSlab T ∧ 0 < timeZeroDist z
    · exact ((SlabSpace.blockProj A hA g).mem_inf hz.1 hz.2).2
    · rw [(SlabSpace.blockProj A hA g).apply_eq_zero hz]
      exact Submodule.zero_mem _
  hf := (SlabSpace.blockProj A hA g).singularBoundOn_norm
  hf0 z hz := (SlabSpace.blockProj A hA g).apply_eq_zero fun h => hz h.1
  hα z i h := by
    refine hAζ i ?_
    by_contra hi
    rw [SlabSpace.val_blockProj] at h
    exact h (blockProj_apply_of_notMem hi _)
  hαγ := hζγ
  hαη := hζη
  hCf := norm_nonneg _

end Model

end RegularityStructures

end
