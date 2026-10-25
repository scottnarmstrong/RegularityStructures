/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Slab.BlockProjMap
public import RegularityStructures.Abstract.Model

/-!
# Structural block invariance

The block-projected fixed point (`exists_unique_phi4_timeSlab_fixedPoint_of_blockOperator_near`)
assumes, model by model, that `Γ_{xy}`
commutes with the coordinate projection `blockProj A` (`hA`).  When this holds for every element
of the structure group (`RegularityStructure.IsBlockInvariant`), it holds for every model, since
`Γ_{xy} ∈ G`; then `hA` is not a hypothesis on the model at all.  The criterion
`isBlockInvariant_univ_erase`: if a symbol `ξ` is fixed by `G` and no `Γ e_i`, `i ≠ ξ`, has a
`ξ`-component, then `A = univ \ {ξ}` is block invariant.  For `Φ⁴₃`, `ξ = Ξ` and `A` = the
`Ξ`-free symbols.
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every element of the structure group commutes with the block projection `blockProj A`. -/
def RegularityStructure.IsBlockInvariant (𝒯 : RegularityStructure ι) (A : Finset ι) : Prop :=
  ∀ g ∈ 𝒯.group, ∀ τ : ι → ℝ,
    ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (blockProj A τ) =
      blockProj A (((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) τ)

variable {𝒯 : RegularityStructure ι}

/-- Structural block invariance gives the per-model hypothesis `hA` of the block-projected fixed
point. -/
theorem Model.gammaMap_blockProj_of_isBlockInvariant {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] {μ : MeasureTheory.Measure E} {K : RegularisingSemigroup E μ}
    {A : Finset ι} (hA : 𝒯.IsBlockInvariant A) (M : Model 𝒯 K) (x y : E) (τ : ι → ℝ) :
    M.gammaMap x y (blockProj A τ) = blockProj A (M.gammaMap x y τ) :=
  hA _ (M.gamma x y).2 τ

/-- **Criterion.** If `ξ` is fixed by the structure group and no `Γ e_i` with `i ≠ ξ` has a
`ξ`-component, then the complement of `{ξ}` is block invariant. -/
theorem isBlockInvariant_univ_erase {ξ : ι}
    (hfix : ∀ g ∈ 𝒯.group,
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single ξ 1) =
        Pi.single ξ 1)
    (hrow : ∀ g ∈ 𝒯.group, ∀ i : ι, i ≠ ξ →
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single i 1) ξ = 0) :
    𝒯.IsBlockInvariant (Finset.univ.erase ξ) := by
  intro g hg τ
  set L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) with hL
  have hproj : ∀ σ : ι → ℝ, blockProj (Finset.univ.erase ξ) σ = σ - σ ξ • Pi.single ξ 1 := by
    intro σ
    funext i
    by_cases hi : i = ξ
    · subst hi
      simp [blockProj_apply]
    · simp [blockProj_apply, hi]
  have hcoord : ∀ σ : ι → ℝ, L σ ξ = σ ξ := by
    intro σ
    have hσ : σ = ∑ i, σ i • (Pi.single i 1 : ι → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hrow' : ∀ i, L (Pi.single i 1) ξ = if i = ξ then 1 else 0 := by
      intro i
      by_cases hi : i = ξ
      · subst hi
        rw [hL, hfix g hg]
        simp
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hi)]
        exact hrow g hg i hi
    conv_lhs => rw [hσ]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hrow']
    simp
  rw [hproj, hproj, map_sub, map_smul, hL, hfix g hg, ← hL, hcoord]

end RegularityStructures

end
