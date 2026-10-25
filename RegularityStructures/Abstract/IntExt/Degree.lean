/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Basic
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Degree bounds for the polynomial corrections of the extended group

`J(x)` raises degrees by less than `2`: if every nonzero coordinate of `a` has degree `≤ β`, then
`J(x) a ∈ T_{<β+2}` (`jMapP_mem_lowerSubspace_of_le`).  The coordinates of `Γ e_i` have degree
`≤ deg i` (`gammaMap_single_ne_zero_deg_le`), and `liftOld` preserves `T_{<α}`.  These give the
degree condition of `IntegrationExtension.mem_group` for the extended model's `Γ'`.
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem jVecP_mem_lowerSubspace (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    {N' : ℕ} (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) (i : ι) :
    jVecP M h P x i ∈ lowerSubspace 𝒯.deg (𝒯.deg i + 2) := by
  classical
  unfold jVecP
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs with hk
  · exact Submodule.smul_mem _ _ (single_mem_lowerSubspace (by rw [P.deg_emb]; exact hk) 1)
  · exact Submodule.zero_mem _

theorem jMapP_mem_lowerSubspace_of_le (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    {N' : ℕ} (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) {β : ℝ} {a : ι → ℝ}
    (ha : ∀ i, a i ≠ 0 → 𝒯.deg i ≤ β) : jMapP M h P x a ∈ lowerSubspace 𝒯.deg (β + 2) := by
  change ∑ i, a i • jVecP M h P x i ∈ _
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : a i = 0
  · simp [hi]
  · exact Submodule.smul_mem _ _
      (lowerSubspace_mono (by linarith [ha i hi]) (jVecP_mem_lowerSubspace M h P x i))

theorem Model.gammaMap_single_ne_zero_deg_le {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : MeasureTheory.Measure E} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K) (x y : E)
    (i j : ι) (hj : M.gammaMap x y (Pi.single i 1) j ≠ 0) : 𝒯.deg j ≤ 𝒯.deg i := by
  by_contra hlt
  push Not at hlt
  have hji : j ≠ i := by rintro rfl; exact lt_irrefl _ hlt
  exact hj ((M.isGradedUnipotent_gammaMap x y).apply_single_of_le hji hlt.le)

omit [DecidableEq ι] in
theorem IntExt.liftOld_mem_lowerSubspace {ι' : Type*} [DecidableEq ι'] {deg : ι → ℝ}
    {deg' : ι' → ℝ} {old : ι → ι'} (hold : Function.Injective old)
    (hdeg : ∀ i, deg' (old i) = deg i) {α : ℝ} {v : ι → ℝ} (hv : v ∈ lowerSubspace deg α) :
    IntExt.liftOld old v ∈ lowerSubspace deg' α := by
  intro j hj
  by_cases h : ∃ i, old i = j
  · obtain ⟨i, rfl⟩ := h
    rw [IntExt.liftOld_apply_old hold]
    exact hv i (by rw [← hdeg]; exact hj)
  · push Not at h
    exact IntExt.liftOld_apply_of_notMem v h

end RegularityStructures

end
