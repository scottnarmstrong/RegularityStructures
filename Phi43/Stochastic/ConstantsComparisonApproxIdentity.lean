/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonConvolution
public import Phi43.Torus.KernelBoundsSupport
public import Phi43.Torus.KernelBoundsCovariance
import Mathlib.Analysis.Convolution
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Shrinking supports for the periodised mollifier

The signed approximate-identity argument in the comparison of the constants uses
`dist_convolution_le'`, whose kernel need not be nonnegative.  This file supplies the geometric
input for that theorem: the support of the periodised parabolic mollifier tends to the singleton
`{0}` in the small-sets filter.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Metric Set
open scoped Topology

namespace RegularityStructures.Phi43

private theorem torusParabolicSize_time_le_sq (z : SpaceTime) :
    |z.1| ≤ torusParabolicSize z ^ 2 := by
  have hs := Real.sq_sqrt (abs_nonneg z.1)
  have hroot : 0 ≤ √|z.1| := Real.sqrt_nonneg _
  have hsp : 0 ≤ torusSpatialNorm z.2 := torusSpatialNorm_nonneg z.2
  unfold torusParabolicSize at hs ⊢
  nlinarith [sq_nonneg (torusSpatialNorm z.2), mul_nonneg hroot hsp]

private theorem torusParabolicSize_dist_space_le (z : SpaceTime) :
    dist z.2 0 ≤ torusParabolicSize z := by
  apply (dist_pi_le_iff').2
  intro i
  have hi := torusSpatialNorm_coord_dist_le z.2 (torusSpatialNorm z.2) (by rfl) i
  have hs : torusSpatialNorm z.2 ≤ torusParabolicSize z := by
    exact le_add_of_nonneg_left (Real.sqrt_nonneg |z.1|)
  simpa using hi.trans hs

theorem constantsComparison_periodise_support_smallSets
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    Tendsto (fun ε : ℝ => Function.support (periodise ρ ε)) (𝓝[>] 0)
      (𝓝 (0 : SpaceTime)).smallSets := by
  obtain ⟨B, hB, hsupport⟩ := periodise_support_parabolic_bound ρ hρ
  rw [tendsto_smallSets_iff]
  intro U hU
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  let q : ℝ := min 1 (min 1 δ / B)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  filter_upwards [Ioo_mem_nhdsGT hq] with ε hε
  have hεpos : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := by
    exact (hε.2.trans_le (min_le_left 1 (min 1 δ / B))).le
  have hBεδ : B * ε < δ := by
    have hqδ : q ≤ δ / B := by
      dsimp [q]
      exact (min_le_right 1 (min 1 δ / B)).trans
        (div_le_div_of_nonneg_right (min_le_right 1 δ) hB.le)
    have hεδ : ε < δ / B := lt_of_lt_of_le hε.2 hqδ
    rw [lt_div_iff₀ hB] at hεδ
    simpa [mul_comm] using hεδ
  have hBε : B * ε < 1 := by
    have hq1 : q ≤ 1 / B := by
      dsimp [q]
      exact (min_le_right 1 (min 1 δ / B)).trans
        (div_le_div_of_nonneg_right (min_le_left 1 δ) hB.le)
    have hεq : ε < 1 / B := lt_of_lt_of_le hε.2 hq1
    rw [lt_div_iff₀ hB] at hεq
    simpa [mul_comm] using hεq
  intro z hz
  have hzP : periodise ρ ε z ≠ 0 := hz
  have hsize : torusParabolicSize z ≤ B * ε := hsupport hεpos hε1 z hzP
  have hsize1 : torusParabolicSize z ≤ 1 := le_of_lt (lt_of_le_of_lt hsize hBε)
  have htime : |z.1| < δ := by
    have hsquare : torusParabolicSize z ^ 2 ≤ torusParabolicSize z := by
      nlinarith [torusParabolicSize_nonneg z]
    exact lt_of_le_of_lt ((torusParabolicSize_time_le_sq z).trans hsquare)
      (hsize.trans_lt hBεδ)
  have hspace : dist z.2 0 < δ :=
    (torusParabolicSize_dist_space_le z).trans_lt (hsize.trans_lt hBεδ)
  have hspace' : ‖z.2‖ < δ := by simpa using hspace
  apply hδU
  simpa [mem_ball, Prod.norm_def, Real.dist_eq] using max_lt htime hspace'

theorem constantsComparison_periodise_convolution_tendsto_of_continuous_compactSupport
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (g : SpaceTime → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g) (x : SpaceTime) :
    Tendsto (fun ε : ℝ => spaceTimeConvolution (periodise ρ ε) g x) (𝓝[>] 0)
      (𝓝 (g x)) := by
  let B : ℝ := ∫ z : ParabolicSpace, |ρ z|
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => abs_nonneg _)
  have hBmass : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∫ z : SpaceTime, |periodise ρ ε z| ≤ B := by
    intro ε hε hε1
    dsimp [B]
    calc
      ∫ z : SpaceTime, |periodise ρ ε z| ≤
          ∫ z : ParabolicSpace, |rescale ρ ε z| :=
        integral_norm_periodise_le ρ hρ hε
      _ = ∫ z : ParabolicSpace, |ρ z| := integral_norm_rescale_eq ρ hρ hε
  have hgu : UniformContinuous g :=
    hg.uniformContinuous_of_tendsto_cocompact hgs.is_zero_at_infty
  rw [Metric.tendsto_nhds]
  intro η hη
  let η' : ℝ := η / (B + 1)
  have hB1 : 0 < B + 1 := by linarith
  have hη' : 0 < η' := div_pos hη hB1
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 hgu η' hη'
  have hsupp : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Function.support (periodise ρ ε) ⊆ Metric.ball (0 : SpaceTime) δ :=
    (tendsto_smallSets_iff.1 (constantsComparison_periodise_support_smallSets ρ hρ)
      (Metric.ball (0 : SpaceTime) δ) (Metric.ball_mem_nhds _ hδ))
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ≤ 1 := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsupp, hpos, hle] with ε hεsupp hε hε1
  have hif : Integrable (periodise ρ ε) := integrable_periodise ρ hρ hε
  have hlocal : ∀ y ∈ Metric.ball x δ, dist (g y) (g x) ≤ η' := by
    intro y hy
    exact (hδg hy).le
  have hdist := dist_convolution_le'
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure SpaceTime))
    (f := periodise ρ ε) (g := g) (x₀ := x) (R := δ) (ε := η') hη'.le hif hεsupp
      hg.aestronglyMeasurable hlocal
  have hmass : ∫ t : SpaceTime, periodise ρ ε t = 1 :=
    constantsComparison_periodise_mass ρ hρ hε
  have hdist' : dist (spaceTimeConvolution (periodise ρ ε) g x) (g x) ≤
      (∫ t : SpaceTime, |periodise ρ ε t|) * η' := by
    simpa [spaceTimeConvolution, MeasureTheory.convolution, smul_eq_mul,
      integral_mul_const, hmass, Real.norm_eq_abs,
      ContinuousLinearMap.opNorm_lsmul] using hdist
  have hbound : (∫ t : SpaceTime, |periodise ρ ε t|) * η' < η := by
    have hfirst : (∫ t : SpaceTime, |periodise ρ ε t|) * η' ≤ B * η' :=
      mul_le_mul_of_nonneg_right (hBmass hε hε1) (le_of_lt hη')
    have hsecond : B * η' < η := by
      dsimp [η']
      rw [show B * (η / (B + 1)) = (B * η) / (B + 1) by ring]
      apply (div_lt_iff₀ hB1).2
      nlinarith [hη, hB]
    exact hfirst.trans_lt hsecond
  exact hdist'.trans_lt hbound

end RegularityStructures.Phi43

end
