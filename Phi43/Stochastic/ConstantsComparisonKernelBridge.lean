/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import RegularityStructures.PDE.TorusLift
public import RegularityStructures.Probability.SpaceTimeMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.NhdsWithin
public import RegularityStructures.Analysis.Heat.Kernel
public import RegularityStructures.Torus.KernelBoundsGaussian

/-!
# The Euclidean heat decomposition behind the torus comparison

This module records the exact algebraic bridge between the torus massive heat kernel and the
spatial periodisation of the Euclidean heat kernel.  It is the point at which the annihilating
shell decomposition enters the comparison of the constants.  The identities are stated before any
integrability estimate; the latter must still control the resulting periodised order-one term.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.Phi43

private noncomputable def bridgeIntegerBox : Finset (Fin 3 → ℤ) := by
  classical
  exact (Finset.univ.pi (fun _ : Fin 3 => Finset.Icc (-3 : ℤ) 3)).image
    (fun q i => q i (Finset.mem_univ i))

private theorem bridge_hairerKernel_zero_of_one_lt {N : ℕ} {z : ParabolicSpace}
    (hz : 1 < parabolicNorm z) : hairerKernel N z = 0 := by
  unfold hairerKernel
  have hzero : ∀ n, annShellC N n z = 0 := by
    intro n
    apply annShellC_eq_zero
    have hscale : (2 : ℝ)⁻¹ ^ n ≤ 1 := by
      exact pow_le_one₀ (by positivity) (by norm_num)
    exact lt_of_le_of_lt hscale hz
  rw [tsum_eq_sum (s := (∅ : Finset ℕ)) (fun n _ => hzero n)]
  simp

private theorem bridge_hairerKernel_support_le_one {N : ℕ} {z : ParabolicSpace}
    (hz : hairerKernel N z ≠ 0) : parabolicNorm z ≤ 1 := by
  by_contra h
  exact hz (bridge_hairerKernel_zero_of_one_lt (lt_of_not_ge h))

private theorem bridge_contributing_integer_mem_box {N : ℕ} {z : SpaceTime}
    {k : Fin 3 → ℤ}
    (hk : hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ)) ≠ 0) :
    k ∈ bridgeIntegerBox := by
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int z.2
  have hs := bridge_hairerKernel_support_le_one hk
  have hcoord : ∀ i : Fin 3,
      |torusRep z.2 i + (k i : ℝ)| ≤ 1 := by
    intro i
    have hsum : |torusRep z.2 i + (k i : ℝ)| ≤
        ∑ j, |torusRep z.2 j + (k j : ℝ)| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j =>
        |torusRep z.2 j + (k j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hpar : √|z.1| + ∑ j, |torusRep z.2 j + (k j : ℝ)| ≤ 1 := by
      simpa [parabolicNorm] using hs
    by_contra hi
    have hi' : 1 < |torusRep z.2 i + (k i : ℝ)| := lt_of_not_ge hi
    linarith [Real.sqrt_nonneg |z.1|]
  classical
  apply Finset.mem_image.mpr
  refine ⟨(fun i _ => k i), ?_, ?_⟩
  · apply Finset.mem_pi.mpr
    intro i hi
    apply Finset.mem_Icc.mpr
    have hcenter := torusCenteredRep_mem_Icc z.2 i
    have hi' : torusRep z.2 i + (k i : ℝ) =
        torusCenteredRep z.2 i + ((m i + k i : ℤ) : ℝ) := by
      rw [hm]
      simp only [Pi.add_apply, Int.cast_add]
      ring
    have hcoord_i := hcoord i
    rw [hi'] at hcoord_i
    have hq : (-2 : ℝ) ≤ (m i + k i : ℤ) ∧
        ((m i + k i : ℤ) : ℝ) ≤ 2 := by
      have hcoord_le := (abs_le.mp hcoord_i)
      constructor <;> linarith [hcoord_le.1, hcoord_le.2, hcenter.1, hcenter.2]
    have hq' : (-2 : ℤ) ≤ m i + k i ∧ m i + k i ≤ (2 : ℤ) := by
      exact_mod_cast hq
    have hm_i : (0 : ℤ) ≤ m i ∧ m i ≤ 1 := by
      have hrep := torusRep_mem_Ico z.2 i
      have heq : (m i : ℝ) = torusRep z.2 i - torusCenteredRep z.2 i := by
        have hi'' := congrFun hm i
        simp only [Pi.add_apply] at hi''
        linarith
      have hlo : (-1 : ℝ) < (m i : ℝ) := by linarith [hrep.1, hcenter.2, heq]
      have hhi : (m i : ℝ) < 2 := by linarith [hrep.2, hcenter.1, heq]
      have hlo' : (-1 : ℤ) < m i := by exact_mod_cast hlo
      have hhi' : m i < (2 : ℤ) := by exact_mod_cast hhi
      constructor <;> omega
    have hki : (-3 : ℤ) ≤ k i ∧ k i ≤ (3 : ℤ) := by
      constructor <;> omega
    exact hki
  · funext i
    simp

private theorem bridge_hairerKernel_periodisation_summable (N : ℕ) (z : SpaceTime) :
    Summable (fun k : Fin 3 → ℤ =>
      hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ))) := by
  apply summable_of_hasFiniteSupport
  refine bridgeIntegerBox.finite_toSet.subset ?_
  intro k hk
  exact bridge_contributing_integer_mem_box (by simpa [Function.mem_support] using hk)

private theorem bridge_heatKernel_periodisation_summable (z : SpaceTime) :
    Summable (fun k : Fin 3 → ℤ =>
      Real.exp (-z.1) * heatKernelR4
        (z.1, torusRep z.2 + fun i => (k i : ℝ))) := by
  by_cases ht : 0 < z.1
  · have hs := summable_gaussKernel_shift ht (torusRep z.2)
      (fun i => torusRep_mem_Ico z.2 i)
    have hs' := hs.mul_left (Real.exp (-z.1))
    exact hs'.congr fun k => by rw [heatKernelR4_of_pos ht]
  · have hzero : ∀ k : Fin 3 → ℤ,
        Real.exp (-z.1) * heatKernelR4
          (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
      intro k
      rw [heatKernelR4_of_nonpos (le_of_not_gt ht), mul_zero]
    exact summable_zero.congr (fun k => (hzero k).symm)

private theorem spaceTime_punctured_nhds_neBot :
    (𝓝[≠] (0 : SpaceTime)).NeBot := by
  rw [nhdsWithin_neBot]
  intro U hU
  rcases (mem_nhds_prod_iff (x := (0 : ℝ)) (y := (0 : Torus3))).1 hU with
    ⟨u, hu, v, hv, huv⟩
  obtain ⟨δ, hδ, hδu⟩ := Metric.mem_nhds_iff.1 hu
  let t : ℝ := δ / 2
  have ht : t ∈ u := hδu (by
    simp only [Metric.mem_ball, Real.dist_eq]
    exact max_lt (by dsimp [t]; linarith) (by dsimp [t]; linarith))
  refine ⟨(t, 0), huv ⟨ht, mem_of_mem_nhds hv⟩, ?_⟩
  dsimp [t]
  simp [hδ.ne']

private theorem massiveHeatKernel_eq_periodised_heatKernelR4 (z : SpaceTime) :
    massiveHeatKernel z =
      ∑' k : Fin 3 → ℤ,
        Real.exp (-z.1) * heatKernelR4
          (z.1, torusRep z.2 + fun i => (k i : ℝ)) := by
  by_cases ht : 0 < z.1
  · simp only [massiveHeatKernel, ht, ite_true, heatKernel, heatKernelR4]
    rw [tsum_mul_left]
  · have ht' : z.1 ≤ 0 := le_of_not_gt ht
    have hzero : ∀ k : Fin 3 → ℤ,
        heatKernelR4 (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
      intro k
      exact heatKernelR4_of_nonpos ht'
    simp only [massiveHeatKernel, ht, ite_false, hzero, mul_zero, tsum_zero]

theorem constantsComparisonR_eq_periodised_orderOne_ae (N : ℕ) :
    ∀ᵐ z : SpaceTime ∂volume,
      constantsComparisonR N z =
        ∑' k : Fin 3 → ℤ,
          ((Real.exp (-z.1) - 1) * heatKernelR4
              (z.1, torusRep z.2 + fun i => (k i : ℝ)) +
            annRemainderC N
              (z.1, torusRep z.2 + fun i => (k i : ℝ))) := by
  have hnull : NullSingletonClass (volume : Measure SpaceTime) :=
    @Measure.IsAddHaarMeasure.nullSingletonClass SpaceTime _ _ _ _ _ _ _
      spaceTime_punctured_nhds_neBot volume inferInstance
  filter_upwards [@Measure.ae_ne SpaceTime _ volume hnull (0 : SpaceTime)] with z hz
  rw [constantsComparisonR, massiveHeatKernel_eq_periodised_heatKernelR4]
  unfold hairerKernelTorus
  have hsumG := bridge_heatKernel_periodisation_summable z
  have hsumK := bridge_hairerKernel_periodisation_summable N z
  rw [← hsumG.tsum_sub hsumK]
  apply tsum_congr
  intro k
  by_cases harg : (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0
  · have hz1 : z.1 = 0 := congrArg Prod.fst harg
    have harg2 : torusRep z.2 + (fun i : Fin 3 => (k i : ℝ)) = 0 :=
      congrArg Prod.snd harg
    have htorus : torusProj (torusRep z.2 + (fun i : Fin 3 => (k i : ℝ))) = 0 := by
      rw [harg2, RegularityStructures.PDE.torusProj_zero]
    have hki : torusProj (fun i : Fin 3 => (k i : ℝ)) = 0 := by
      funext i
      simp [torusProj]
    have hz2 : z.2 = 0 := by
      rw [RegularityStructures.PDE.torusProj_add,
        RegularityStructures.PDE.torusProj_torusRep, hki, add_zero] at htorus
      exact htorus
    exact (hz (Prod.ext hz1 hz2)).elim
  · rw [hairerKernel_eq_heat_sub_remainder harg]
    ring
end RegularityStructures.Phi43

end
