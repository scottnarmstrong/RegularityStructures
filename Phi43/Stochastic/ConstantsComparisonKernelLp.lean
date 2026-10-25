/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonSingularLp
public import RegularityStructures.Probability.SpaceTimeMeasure
public import RegularityStructures.Torus.HeatKernelFacts
public import RegularityStructures.PDE.TorusLift
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import Phi43.Stochastic.ConstantsComparisonKernelBounds
public import RegularityStructures.Analysis.Parabolic.SmoothNorm

/-!
# Measurability and integrability of the periodised Hairer kernel

The annihilating shells are measurable and locally finite at every point, so their `tsum` is
measurable.  The torus periodisation has the same singular order as the Euclidean kernel and is
supported in the unit parabolic ball.  This file turns those pointwise facts into the `L¹` input
needed by the comparison of the constants in Section 7 of the statement.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem measurable_constantsComparison_hairerKernel (N : ℕ) :
    Measurable (hairerKernel N) := by
  unfold hairerKernel
  exact Measurable.tsum fun n => (contDiff_annShellC N n).continuous.measurable

theorem measurable_constantsComparison_hairerKernelTorus (N : ℕ) :
    Measurable (hairerKernelTorus N) := by
  unfold hairerKernelTorus
  apply Measurable.tsum
  intro k
  apply (measurable_constantsComparison_hairerKernel N).comp
  exact measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const)

private theorem constantsComparison_hairerKernel_zero_of_one_lt {N : ℕ} {z : ParabolicSpace}
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

private theorem constantsComparison_centered_lift_size_le {x : Torus3} (k : Fin 3 → ℤ) :
    torusSpatialNorm x ≤ √(sqNorm3 (torusRep x + fun i => (k i : ℝ))) := by
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int x
  have hcoord : ∀ i : Fin 3,
      (torusCenteredRep x i) ^ 2 ≤
        (torusRep x i + (k i : ℝ)) ^ 2 := by
    intro i
    have hsq := sq_centered_add_int_ge (torusCenteredRep_mem_Icc x i) (m i + k i)
    have hi : torusRep x i + (k i : ℝ) =
        torusCenteredRep x i + ((m i + k i : ℤ) : ℝ) := by
      rw [hm]
      simp only [Pi.add_apply, Int.cast_add]
      ring
    rw [← hi] at hsq
    exact hsq
  have hsum : sqNorm3 (torusCenteredRep x) ≤
      sqNorm3 (torusRep x + fun i => (k i : ℝ)) := by
    unfold sqNorm3
    exact Finset.sum_le_sum fun i _ => hcoord i
  unfold torusSpatialNorm
  exact Real.sqrt_le_sqrt hsum

private theorem constantsComparison_centered_lift_size_le_parabolic {z : SpaceTime}
    (k : Fin 3 → ℤ) :
    torusParabolicSize z ≤
      parabolicNorm (z.1, torusRep z.2 + fun i => (k i : ℝ)) := by
  unfold torusParabolicSize parabolicNorm
  have hsp := constantsComparison_centered_lift_size_le (x := z.2) k
  have hroot : √(sqNorm3 (torusRep z.2 + fun i => (k i : ℝ))) ≤
      ∑ i, |(torusRep z.2 + fun i => (k i : ℝ)) i| := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold sqNorm3
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin 3 => |(torusRep z.2 + fun i => (k i : ℝ)) i|)
        (fun i _ => abs_nonneg _))
  exact add_le_add le_rfl (hsp.trans hroot)

private theorem constantsComparison_hairerKernelTorus_zero_of_one_lt {N : ℕ}
    {z : SpaceTime} (hz : 1 < torusParabolicSize z) :
    hairerKernelTorus N z = 0 := by
  unfold hairerKernelTorus
  rw [show (fun k : Fin 3 → ℤ =>
      hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ))) = fun _ => 0 by
    funext k
    apply constantsComparison_hairerKernel_zero_of_one_lt
    exact lt_of_lt_of_le hz (constantsComparison_centered_lift_size_le_parabolic k)]
  exact tsum_zero

private theorem constantsComparison_torusParabolicSize_pos_of_ne {z : SpaceTime}
    (hz : z ≠ 0) : 0 < torusParabolicSize z := by
  by_contra hs
  have hs0 : torusParabolicSize z = 0 :=
    le_antisymm (le_of_not_gt hs) (torusParabolicSize_nonneg z)
  have htime : √|z.1| = 0 := by
    unfold torusParabolicSize at hs0
    have hnonneg_sp := torusSpatialNorm_nonneg z.2
    have hnonneg_time := Real.sqrt_nonneg |z.1|
    linarith
  have hsp : torusSpatialNorm z.2 = 0 := by
    unfold torusParabolicSize at hs0
    have hnonneg := Real.sqrt_nonneg |z.1|
    linarith
  have htime' : z.1 = 0 := by
    have hsq := Real.sq_sqrt (abs_nonneg z.1)
    have habs : |z.1| = 0 := by
      calc
        |z.1| = √|z.1| ^ 2 := hsq.symm
        _ = 0 := by rw [htime]; norm_num
    exact abs_eq_zero.mp habs
  have hcenter : torusCenteredRep z.2 = 0 := by
    apply (sqNorm3_eq_zero_iff _).mp
    rw [← torusSpatialNorm_sq]
    rw [hsp]
    norm_num
  have hrep : torusRep z.2 = 0 := by
    funext i
    have hi := congrFun hcenter i
    unfold torusCenteredRep at hi
    split_ifs at hi with hhalf
    · have hrepIco := torusRep_mem_Ico z.2 i
      simp only [Pi.zero_apply] at hi
      have hi' : torusRep z.2 i = 1 := by linarith
      have hrepIco' := hrepIco
      simp only [mem_Ico] at hrepIco'
      linarith
    · exact hi
  have htorus : z.2 = 0 := by
    rw [← RegularityStructures.PDE.torusProj_torusRep z.2, hrep,
      RegularityStructures.PDE.torusProj_zero]
  exact hz (Prod.ext htime' htorus)

private noncomputable def constantsComparisonIntegerBox : Finset (Fin 3 → ℤ) := by
  classical
  exact (Finset.univ.pi (fun _ : Fin 3 => Finset.Icc (-3 : ℤ) 3)).image
    (fun q i => q i (Finset.mem_univ i))

private theorem constantsComparison_contributing_integer_mem_box {N : ℕ} {z : SpaceTime}
    {k : Fin 3 → ℤ}
    (hk : hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ)) ≠ 0) :
    k ∈ constantsComparisonIntegerBox := by
  obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int z.2
  have hs : parabolicNorm
      (z.1, torusRep z.2 + fun i => (k i : ℝ)) ≤ 1 := by
    by_contra h
    exact hk (constantsComparison_hairerKernel_zero_of_one_lt (lt_of_not_ge h))
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
      have hcoord_le := abs_le.mp hcoord_i
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

private theorem constantsComparison_hairerKernelTorus_uniform_singular_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z : SpaceTime}, 0 < torusParabolicSize z →
      |hairerKernelTorus N z| ≤ C * torusParabolicSize z ^ (-(3 : ℝ)) := by
  obtain ⟨C₀, hC₀, hK⟩ := hairerKernel_singular_bound N
  let S := constantsComparisonIntegerBox
  refine ⟨S.card * C₀, by positivity, ?_⟩
  intro z hz
  have hsum : hairerKernelTorus N z =
      ∑ k ∈ S, hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ)) := by
    unfold hairerKernelTorus
    rw [tsum_eq_sum]
    intro k hk
    by_contra hne
    exact hk (constantsComparison_contributing_integer_mem_box hne)
  have hterm : ∀ k ∈ S,
      |hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤
        C₀ * torusParabolicSize z ^ (-(3 : ℝ)) := by
    intro k hk
    by_cases hzero : hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0
    · simpa only [hzero, abs_zero] using
        (mul_nonneg hC₀ (Real.rpow_nonneg (torusParabolicSize_nonneg z) _))
    · have hargne : (z.1, torusRep z.2 + fun i => (k i : ℝ)) ≠ 0 := by
        intro harg
        have hzero_size : parabolicNorm
            (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by simp [harg]
        have hle := constantsComparison_centered_lift_size_le_parabolic (z := z) k
        rw [hzero_size] at hle
        linarith
      have hbound := hK hargne
      have hsize := constantsComparison_centered_lift_size_le_parabolic (z := z) k
      have hpow : parabolicNorm
          (z.1, torusRep z.2 + fun i => (k i : ℝ)) ^ (-(3 : ℝ)) ≤
          torusParabolicSize z ^ (-(3 : ℝ)) := by
        exact Real.rpow_le_rpow_of_nonpos hz hsize (by norm_num)
      calc
        |hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤
            C₀ * parabolicNorm (z.1, torusRep z.2 + fun i => (k i : ℝ)) ^ (-(3 : ℝ)) :=
          hbound
        _ ≤ C₀ * torusParabolicSize z ^ (-(3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow hC₀
  have hsum_abs0 : |hairerKernelTorus N z| ≤
      ∑ k ∈ S, |hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ))| := by
    rw [hsum]
    have hnorm := norm_sum_le S
      (fun k : Fin 3 → ℤ => hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ)))
    simpa only [Real.norm_eq_abs] using hnorm
  calc
    |hairerKernelTorus N z| ≤
        ∑ k ∈ S, C₀ * torusParabolicSize z ^ (-(3 : ℝ)) :=
      hsum_abs0.trans (Finset.sum_le_sum fun k hk => hterm k hk)
    _ = S.card * (C₀ * torusParabolicSize z ^ (-(3 : ℝ))) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
    _ = (S.card * C₀) * torusParabolicSize z ^ (-(3 : ℝ)) := by ring

theorem constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z : SpaceTime}, 0 < torusParabolicSize z →
      |hairerKernelTorus N z| ≤ C * torusParabolicSize z ^ (-(3 : ℝ)) :=
  constantsComparison_hairerKernelTorus_uniform_singular_bound N

theorem constantsComparison_hairerKernelTorus_abs_le_singularWeight {N : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ z : SpaceTime ∂volume,
      |hairerKernelTorus N z| ≤ C * constantsComparisonSingularWeight 3 z := by
  obtain ⟨C, hC, hbound⟩ :=
    constantsComparison_hairerKernelTorus_uniform_singular_bound N
  refine ⟨C, hC, ?_⟩
  filter_upwards [@Measure.ae_ne SpaceTime _ volume
    (Measure.IsAddHaarMeasure.nullSingletonClass volume) (0 : SpaceTime)] with z hz
  have hpos := constantsComparison_torusParabolicSize_pos_of_ne hz
  by_cases hsmall : torusParabolicSize z ≤ 1
  · simpa [constantsComparisonSingularWeight, hpos, hsmall] using hbound hpos
  · have hlarge : 1 < torusParabolicSize z := lt_of_not_ge hsmall
    rw [constantsComparison_hairerKernelTorus_zero_of_one_lt hlarge]
    simp [constantsComparisonSingularWeight, hpos, hsmall]

theorem integrable_constantsComparison_hairerKernelTorus (N : ℕ) :
    Integrable (hairerKernelTorus N) := by
  obtain ⟨C, hC, hbound⟩ := constantsComparison_hairerKernelTorus_abs_le_singularWeight
  have hweight := integrable_constantsComparisonSingularWeight
    (q := (3 : ℝ)) (by norm_num) (by norm_num)
  have hmajorant : Integrable (fun z : SpaceTime => C *
      constantsComparisonSingularWeight 3 z) := hweight.const_mul C
  refine Integrable.mono' hmajorant ?_ hbound
  exact (measurable_constantsComparison_hairerKernelTorus N).aestronglyMeasurable

end RegularityStructures.Phi43

end
