/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointSlabSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.Normed.Module.FiniteDimension
public import RegularityStructures.Abstract.Model

/-!
# Completeness of `D^{γ,η}_P(V)` on a time slab

The proof of [Hai14, Theorem 7.8] starts from: "for a fixed model `Z`, the space `D^{γ,η}_P` is a
Banach space". Here this is proved for the slab space `Model.SlabSpace M ρ V γ η S` of
`RegularityStructures.Abstract.FixedPointSlabSpace` (instance `Model.instCompleteSpaceSlabSpace`).

Proof: every coordinate evaluation `u ↦ u(x)_i` is Lipschitz for `|||·|||_{γ,η;S}`
(`Model.SlabSpace.abs_apply_le`), so a Cauchy sequence converges pointwise; the pointwise limit
is measurable, takes values in the closed subspace `V ∩ T_{<γ}` on `S⁺` and vanishes off `S⁺`; the
bounds of `D^{γ,η}_P` pass to pointwise limits (`Model.SingularBoundOn.of_tendsto`), which gives
both membership and convergence in norm.

Source: [Hai14] = arXiv:1303.5113v4, proof of Theorem 7.8.
-/

public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

/-- Coordinates are controlled by the norm:
`|u(x)_i| ≤ |||u|||_{γ,η;S} · |‖x‖_P^{(η − deg i) ∧ 0}|` for every `x` and `i`. -/
theorem SlabSpace.abs_apply_le (u : M.SlabSpace ρ V γ η S) (x : E) (i : ι) :
    |u.val x i| ≤ ‖u‖ * |singularWeight ρ x ^ min (η - 𝒯.deg i) 0| := by
  have hn : 0 ≤ ‖u‖ := norm_nonneg u
  by_cases hx : x ∈ S ∧ 0 < ρ x
  · by_cases hi : 𝒯.deg i < γ
    · exact (u.singularBoundOn_norm.1 x hx.1 hx.2 i hi).trans
        (mul_le_mul_of_nonneg_left (le_abs_self _) hn)
    · rw [(Submodule.mem_inf.1 (u.mem_inf hx.1 hx.2)).2 i (not_lt.1 hi), abs_zero]
      exact mul_nonneg hn (abs_nonneg _)
  · rw [u.apply_eq_zero hx, Pi.zero_apply, abs_zero]
    exact mul_nonneg hn (abs_nonneg _)

/-- Coordinate evaluation is Lipschitz on the slab space. -/
theorem SlabSpace.lipschitzWith_apply (x : E) (i : ι) :
    LipschitzWith ⟨|singularWeight ρ x ^ min (η - 𝒯.deg i) 0|, abs_nonneg _⟩
      (fun u : M.SlabSpace ρ V γ η S => u.val x i) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [Real.dist_eq, dist_eq_norm, mul_comm]
  have h := SlabSpace.abs_apply_le (u - v) x i
  rw [SlabSpace.val_sub, Pi.sub_apply, Pi.sub_apply] at h
  exact h

/-- **`D^{γ,η}_P(V)` on a slab is a Banach space** (used in [Hai14, proof of Theorem 7.8]). -/
instance instCompleteSpaceSlabSpace : CompleteSpace (M.SlabSpace ρ V γ η S) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- pointwise limit
  have hpt : ∀ x i, CauchySeq fun n => (u n).val x i := fun x i =>
    (SlabSpace.lipschitzWith_apply x i).uniformContinuous.comp_cauchySeq hu
  set g : E → ι → ℝ := fun x i => limUnder atTop fun n => (u n).val x i with hg_def
  have hg : ∀ x, Tendsto (fun n => (u n).val x) atTop (𝓝 (g x)) := fun x =>
    tendsto_pi_nhds.2 fun i => (hpt x i).tendsto_limUnder
  -- the bound on `g − u n`
  have key : ∀ ε > 0, ∃ N, ∀ n ≥ N, M.SingularBoundOn ρ γ η ε S (g - (u n).val) := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    refine SingularBoundOn.of_tendsto M (F := fun m => (u m).val - (u n).val)
      (eventually_atTop.2 ⟨N, fun m hm => ?_⟩) fun x => (hg x).sub tendsto_const_nhds
    have h := ((u m - u n).norm_le_iff hε.le).1 (by
      rw [← dist_eq_norm]
      exact (hN m hm n hn).le)
    rwa [SlabSpace.val_sub] at h
  -- membership of the limit
  have hgmem : g ∈ M.slabModelledDistributions ρ V γ η S := by
    refine ⟨measurable_of_tendsto_metrizable (fun n => (u n).measurable)
        (tendsto_pi_nhds.2 hg), fun x hx hρ => ?_, fun x hx => ?_, ?_⟩
    · exact (Submodule.closed_of_finiteDimensional _).mem_of_tendsto (hg x)
        (Eventually.of_forall fun n => (u n).mem_inf hx hρ)
    · refine tendsto_nhds_unique (hg x) ?_
      simp only [SlabSpace.apply_eq_zero _ hx]
      exact tendsto_const_nhds
    · obtain ⟨N, hN⟩ := key 1 one_pos
      refine ⟨1 + ‖u N‖, ?_⟩
      have h := (hN N le_rfl).add M (u N).singularBoundOn_norm
      rwa [sub_add_cancel] at h
  refine ⟨SlabSpace.mk g hgmem, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := key (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have h := (hN n hn).neg M
  rw [neg_sub] at h
  have hle : ‖u n - SlabSpace.mk g hgmem‖ ≤ ε / 2 :=
    (u n - SlabSpace.mk g hgmem).norm_le (half_pos hε).le (by
      rwa [SlabSpace.val_sub, SlabSpace.val_mk])
  exact hle.trans_lt (half_lt_self hε)

end Model

end RegularityStructures

end
