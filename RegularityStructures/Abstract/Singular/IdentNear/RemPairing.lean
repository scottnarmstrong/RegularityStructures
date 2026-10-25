/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.Integrals
public import RegularityStructures.Abstract.Singular.Remainder.Defs

/-!
# `⟨R f, ψ⟩` for a test function without compact support, near-pair `Γ`-bounds

`remPairing f ψ = ∑'_j ⟨R f, ψ χ_{3,j}⟩` sums the lattice reconstructions over the level-3 cells.
For a smooth function model and a continuous `ψ` with `R̃f ψ` integrable, the sum is the integral
`∫ R̃f ψ` (`remPairing_eq_integral_wnear`): each term is `∫ R̃f ψ χ_{3,j}` and the cells form a
partition of unity.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

/-- **`⟨R f, ψ⟩ = ∫ R̃f ψ`** for continuous `ψ` with `R̃f ψ` integrable. -/
theorem remPairing_eq_integral_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {ψ : ParabolicSpace → ℝ} (hψ : Continuous ψ)
    (hint : Integrable (fun y => pointwiseReconstruct g f y * ψ y)) :
    M.remPairing f ψ = ∫ y, pointwiseReconstruct g f y * ψ y := by
  classical
  set Φ := pointwiseReconstruct g f with hΦ
  have hcont : ∀ j, Continuous (fun y => ψ y * latticeCell 3 j y) := fun j =>
    hψ.mul (contDiff_latticeCell 3 j).continuous
  have hcs : ∀ j, HasCompactSupport (fun y => ψ y * latticeCell 3 j y) := fun j =>
    (hasCompactSupport_latticeCell 3 j).mul_left
  have hF : ∀ j, M.latticeRecon f (fun y => ψ y * latticeCell 3 j y) =
      ∫ y, Φ y * (ψ y * latticeCell 3 j y) := fun j =>
    latticeRecon_eq_integral_wnear hg S (hcont j) (hcs j)
  have hFint : ∀ j, Integrable (fun y => Φ y * (ψ y * latticeCell 3 j y)) := fun j =>
    integrable_pointwiseReconstruct_mul_wnear hg S (hcont j) (hcs j)
  have hle : ∀ (s : Finset LatticeIndex) (y : ParabolicSpace),
      ∑ j ∈ s, latticeCell 3 j y ≤ 1 := by
    intro s y
    set t := (finite_support_latticeCell 3 y).toFinset with ht
    have h1 : ∑ j ∈ s ∪ t, latticeCell 3 j y = 1 := sum_latticeCell_eq_one fun k hk =>
      Finset.mem_union_right _ (by simpa [ht, Set.Finite.mem_toFinset] using hk)
    rw [← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun j _ _ => latticeCell_nonneg _ _ _
  have hsum : Summable fun j => ∫ y, ‖Φ y * (ψ y * latticeCell 3 j y)‖ := by
    refine summable_of_sum_le (c := ∫ y, ‖Φ y * ψ y‖) (fun j => integral_nonneg fun y =>
      norm_nonneg _) fun s => ?_
    rw [← integral_finsetSum _ fun j _ => (hFint j).norm]
    refine integral_mono (integrable_finsetSum _ fun j _ => (hFint j).norm) hint.norm
      fun y => ?_
    simp only [Real.norm_eq_abs, abs_mul]
    calc ∑ j ∈ s, |Φ y| * (|ψ y| * |latticeCell 3 j y|)
        = |Φ y| * |ψ y| * ∑ j ∈ s, latticeCell 3 j y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_of_nonneg (latticeCell_nonneg _ _ _)]; ring
      _ ≤ |Φ y| * |ψ y| * 1 := mul_le_mul_of_nonneg_left (hle s y)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |Φ y| * |ψ y| := mul_one _
  have hHS := hasSum_integral_of_summable_integral_norm hFint hsum
  have htsum : ∀ y, ∑' j, Φ y * (ψ y * latticeCell 3 j y) = Φ y * ψ y := by
    intro y
    have e1 : ∑' j, Φ y * (ψ y * latticeCell 3 j y) = Φ y * ψ y * ∑' j, latticeCell 3 j y := by
      rw [← tsum_mul_left]
      exact tsum_congr fun j => by ring
    rw [e1, tsum_eq_finsum (finite_support_latticeCell 3 y), finsum_latticeCell, mul_one]
  have hrem : M.remPairing f ψ = ∑' j, ∫ y, Φ y * (ψ y * latticeCell 3 j y) := by
    unfold remPairing
    exact tsum_congr hF
  rw [hrem]
  have h := hHS.tsum_eq
  simp only [htsum] at h
  exact h

end Model

end RegularityStructures
