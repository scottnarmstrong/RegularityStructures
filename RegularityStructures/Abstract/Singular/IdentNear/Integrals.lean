/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.Recon
public import RegularityStructures.Abstract.Singular.Ident.Integrals
public import RegularityStructures.Abstract.Singular.Ident.DomIntegrable

/-!
# Measurability and integrability of the pointwise reconstruction, near-pair `Γ`-bounds

Let `Φ = pointwiseReconstruct g f`. Then `|Φ y| ≤ identDom y`
(`abs_pointwiseReconstruct_le_identDom_wnear`); `Φ ψ` is a.e. strongly measurable for every
continuous `ψ` (`aestronglyMeasurable_pointwiseReconstruct_mul_wnear`); and `Φ ψ` is integrable for
`ψ` continuous with compact support (`integrable_pointwiseReconstruct_mul_wnear`).

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

theorem abs_pointwiseReconstruct_le_identDom_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (y : ParabolicSpace) :
    |pointwiseReconstruct g f y| ≤ identDom 𝒯 g γ η Cf CGam y := by
  have h := ((tendsto_latticeAvg_wnear hg S y).comp (tendsto_add_atTop_nat 1)).abs
  exact le_of_tendsto h (Eventually.of_forall fun n =>
    abs_latticeAvg_le_wnear hg S (Nat.le_add_left 1 n) y)

/-- `Φ ψ` is a.e. strongly measurable for continuous compactly supported `ψ`. -/
theorem aestronglyMeasurable_pointwiseReconstruct_mul_of_compact_wnear
    (hg : M.IsSmoothFunctionModelBelow g γ) (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {ψ : ParabolicSpace → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    AEStronglyMeasurable (fun y => pointwiseReconstruct g f y * ψ y) volume := by
  choose F hFc hFe hFi using fun n => exists_continuous_eq_latticeApprox_wnear hg S hψ hψc n
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => F (n + 1))
    (fun n => (hFc (n + 1)).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  simp only [hFe]
  exact ((tendsto_latticeAvg_wnear hg S y).comp (tendsto_add_atTop_nat 1)).mul_const _

/-- `Φ ψ` is integrable for continuous compactly supported `ψ` (`min(η, 0) > -2`). -/
theorem integrable_pointwiseReconstruct_mul_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {ψ : ParabolicSpace → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) : Integrable (fun y => pointwiseReconstruct g f y * ψ y) := by
  have hη : -2 < min η 0 := lt_min (lt_of_lt_of_le S.hαη (min_le_right _ _)) (by norm_num)
  refine (integrable_abs_mul_identDom (M := M) (g := g) (γ := γ) (η := η) (Cf := Cf)
    (CGam := CGam) hg hη S.hCf hψ hψc).mono'
    (aestronglyMeasurable_pointwiseReconstruct_mul_of_compact_wnear hg S hψ hψc)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_pointwiseReconstruct_le_identDom_wnear hg S y) (abs_nonneg _)

/-- `Φ ψ` is a.e. strongly measurable for every continuous `ψ`. -/
theorem aestronglyMeasurable_pointwiseReconstruct_mul_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {ψ : ParabolicSpace → ℝ} (hψ : Continuous ψ) :
    AEStronglyMeasurable (fun y => pointwiseReconstruct g f y * ψ y) volume := by
  classical
  have hcell : ∀ j, AEStronglyMeasurable
      (fun y => pointwiseReconstruct g f y * (ψ y * latticeCell 3 j y)) volume := fun j =>
    aestronglyMeasurable_pointwiseReconstruct_mul_of_compact_wnear hg S
      (hψ.mul (contDiff_latticeCell 3 j).continuous) (hasCompactSupport_latticeCell 3 j).mul_left
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset LatticeIndex))
    (f := fun s y => ∑ j ∈ s, pointwiseReconstruct g f y * (ψ y * latticeCell 3 j y))
    (fun s => ?_) (Eventually.of_forall fun y => ?_)
  · exact Finset.aestronglyMeasurable_fun_sum s fun j _ => hcell j
  · refine tendsto_atTop_of_eventually_const (i₀ := (finite_support_latticeCell 3 y).toFinset)
      fun s hs => ?_
    have h1 : ∑ j ∈ s, latticeCell 3 j y = 1 := sum_latticeCell_eq_one fun k hk =>
      hs (by simpa [Set.Finite.mem_toFinset] using hk)
    calc ∑ j ∈ s, pointwiseReconstruct g f y * (ψ y * latticeCell 3 j y)
        = pointwiseReconstruct g f y * ψ y * ∑ j ∈ s, latticeCell 3 j y := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [h1, mul_one]

end Model

end RegularityStructures
