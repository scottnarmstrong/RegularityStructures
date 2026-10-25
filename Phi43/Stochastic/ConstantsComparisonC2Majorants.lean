/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonCovarianceUniform
public import Phi43.Stochastic.ConstantsComparisonC2Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Phi43.Stochastic.ConstantsComparisonRemainderBound
public import RegularityStructures.Analysis.Parabolic.SmoothNorm

/-!
# Dominating functions for the second-constant comparison

The two terms of the difference of Hairer's (10.41) are bounded by integrable weights of
orders three and four, respectively, in parabolic dimension five. The tail of the first
term is bounded by the integrable massive kernel. All constants are uniform for `0 < ε ≤ 1`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace RegularityStructures.Phi43

private theorem comparisonC2_size_pos {z : SpaceTime} (hz : z ≠ 0) :
    0 < torusParabolicSize z := by
  by_contra h
  have hs : torusParabolicSize z = 0 :=
    le_antisymm (le_of_not_gt h) (torusParabolicSize_nonneg z)
  have ht : √|z.1| = 0 := by
    unfold torusParabolicSize at hs
    linarith [Real.sqrt_nonneg |z.1|, torusSpatialNorm_nonneg z.2]
  have hx : torusSpatialNorm z.2 = 0 := by
    unfold torusParabolicSize at hs
    linarith [Real.sqrt_nonneg |z.1|]
  have ht0 : z.1 = 0 := by
    have hh := Real.sq_sqrt (abs_nonneg z.1)
    rw [ht] at hh
    exact abs_eq_zero.mp (by simpa using hh.symm)
  have hc : torusCenteredRep z.2 = 0 := by
    apply (sqNorm3_eq_zero_iff _).mp
    rw [← torusSpatialNorm_sq, hx]
    norm_num
  have hx0 : z.2 = 0 := by
    rw [← torusProj_torusCenteredRep z.2, hc]
    ext i
    simp [torusProj]
  exact hz (Prod.ext ht0 hx0)

private theorem comparisonC2_covariance_abs_le
    {ρ : ParabolicSpace → ℝ} {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hQ : ∀ z, |covariance ρ ε z| ≤
      C * (torusParabolicSize z + ε) ^ (-(1 : ℝ)))
    {z : SpaceTime} (hz : 0 < torusParabolicSize z) :
    |covariance ρ ε z| ≤ C * torusParabolicSize z ^ (-(1 : ℝ)) := by
  exact (hQ z).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hz (le_add_of_nonneg_right hε.le)
      (by norm_num)) hC)

theorem constantsComparison_C2_first_majorant
    (N : ℕ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    ∃ d : SpaceTime → ℝ, Integrable d ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∀ᵐ z ∂volume, ‖constantsComparisonR N z * covariance ρ ε z ^ 2‖ ≤ d z := by
  obtain ⟨CR, hCR, hR⟩ := constantsComparisonR_orderOne_ae N
  obtain ⟨CQ, hCQ, hQ⟩ := covariance_singular_bound ρ hρ
  obtain ⟨CK, hCK, hK⟩ :=
    constantsComparison_hairerKernelTorus_abs_le_singularWeight (N := N)
  let d : SpaceTime → ℝ := fun z => CR * CQ ^ 2 *
    constantsComparisonSingularWeight 3 z + CQ ^ 2 * massiveHeatKernel z
  have hd : Integrable d :=
    ((integrable_constantsComparisonSingularWeight (q := 3) (by norm_num)
      (by norm_num)).const_mul (CR * CQ ^ 2)).add
        (integrable_massiveHeatKernel.const_mul (CQ ^ 2))
  refine ⟨d, hd, ?_⟩
  intro ε hε hε1
  filter_upwards [hR, hK, @Measure.ae_ne SpaceTime _ volume
    (Measure.IsAddHaarMeasure.nullSingletonClass volume) (0 : SpaceTime)] with z hRz hKz hzne
  have hz := comparisonC2_size_pos hzne
  have hQz := comparisonC2_covariance_abs_le hε hCQ (hQ hε hε1) hz
  have hQsq : covariance ρ ε z ^ 2 ≤
      CQ ^ 2 * (torusParabolicSize z ^ (-(1 : ℝ))) ^ 2 := by
    calc
      covariance ρ ε z ^ 2 = |covariance ρ ε z| ^ 2 := (sq_abs _).symm
      _ ≤ (CQ * torusParabolicSize z ^ (-(1 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hQz 2
      _ = _ := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
  by_cases hs : torusParabolicSize z ≤ 1
  · have hprod : |constantsComparisonR N z| * covariance ρ ε z ^ 2 ≤
        CR * CQ ^ 2 * torusParabolicSize z ^ (-(3 : ℝ)) := by
      calc
        _ ≤ (CR * torusParabolicSize z ^ (-(1 : ℝ))) *
            (CQ ^ 2 * (torusParabolicSize z ^ (-(1 : ℝ))) ^ 2) :=
          mul_le_mul (hRz hz hs) hQsq (sq_nonneg _)
            (mul_nonneg hCR (Real.rpow_nonneg hz.le _))
        _ = CR * CQ ^ 2 * torusParabolicSize z ^ (-(3 : ℝ)) := by
          have hp : (torusParabolicSize z ^ (-(1 : ℝ))) ^ (2 : ℕ) =
              torusParabolicSize z ^ (-(2 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
            norm_num
          rw [hp]
          rw [show (CR * torusParabolicSize z ^ (-(1 : ℝ))) *
              (CQ ^ 2 * torusParabolicSize z ^ (-(2 : ℝ))) =
            CR * CQ ^ 2 * (torusParabolicSize z ^ (-(1 : ℝ)) *
              torusParabolicSize z ^ (-(2 : ℝ))) by ring]
          rw [← Real.rpow_add hz]
          norm_num
    simpa [d, constantsComparisonSingularWeight, hz, hs] using
      hprod.trans (le_add_of_nonneg_right
        (mul_nonneg (sq_nonneg CQ) (massiveHeatKernel_nonneg z)))
  · have hweight : constantsComparisonSingularWeight 3 z = 0 := by
      simp [constantsComparisonSingularWeight, hs]
    have hKzero : hairerKernelTorus N z = 0 :=
      abs_eq_zero.mp (le_antisymm (by simpa [hweight] using hKz) (abs_nonneg _))
    have hp : torusParabolicSize z ^ (-(1 : ℝ)) ≤ 1 := by
      exact (Real.rpow_le_rpow_of_nonpos zero_lt_one (le_of_not_ge hs)
        (by norm_num)).trans_eq (by norm_num)
    have hQz' : |covariance ρ ε z| ≤ CQ :=
      hQz.trans (by simpa using mul_le_mul_of_nonneg_left hp hCQ)
    have hQsq' : covariance ρ ε z ^ 2 ≤ CQ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hQz' 2
    have hp' := mul_le_mul_of_nonneg_left hQsq' (massiveHeatKernel_nonneg z)
    simpa [constantsComparisonR, hKzero, d, hweight,
      abs_of_nonneg (massiveHeatKernel_nonneg z), mul_comm] using hp'

theorem constantsComparison_C2_second_majorant
    (N : ℕ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    ∃ d : SpaceTime → ℝ, Integrable d ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∀ᵐ z ∂volume, ‖hairerKernelTorus N z *
        (covariance ρ ε z - hairerCovariance N ρ ε z) *
        (covariance ρ ε z + hairerCovariance N ρ ε z)‖ ≤ d z := by
  obtain ⟨CQ, hCQ, hQ⟩ := covariance_singular_bound ρ hρ
  obtain ⟨D, hD, hdiff⟩ :=
    constantsComparison_covariance_difference_uniform_bound_unconditional N ρ hρ
  obtain ⟨CK, hCK, hK⟩ :=
    constantsComparison_hairerKernelTorus_abs_le_singularWeight (N := N)
  let A : ℝ := CK * D * (2 * CQ + D)
  refine ⟨fun z => A * constantsComparisonSingularWeight 4 z,
    (integrable_constantsComparisonSingularWeight (q := 4) (by norm_num)
      (by norm_num)).const_mul A, ?_⟩
  intro ε hε hε1
  filter_upwards [hK, @Measure.ae_ne SpaceTime _ volume
    (Measure.IsAddHaarMeasure.nullSingletonClass volume) (0 : SpaceTime)] with z hKz hzne
  have hz := comparisonC2_size_pos hzne
  by_cases hs : torusParabolicSize z ≤ 1
  · have hQz := comparisonC2_covariance_abs_le hε hCQ (hQ hε hε1) hz
    have hDz := hdiff hε hε1 z
    have hKz' : |hairerKernelTorus N z| ≤
        CK * torusParabolicSize z ^ (-(3 : ℝ)) := by
      simpa [constantsComparisonSingularWeight, hz, hs] using hKz
    have hone : 1 ≤ torusParabolicSize z ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      exact (one_le_inv₀ hz).2 hs
    have hsum : |covariance ρ ε z + hairerCovariance N ρ ε z| ≤
        (2 * CQ + D) * torusParabolicSize z ^ (-(1 : ℝ)) := by
      have hid : covariance ρ ε z + hairerCovariance N ρ ε z =
          2 * covariance ρ ε z - (covariance ρ ε z - hairerCovariance N ρ ε z) := by ring
      calc
        _ ≤ 2 * |covariance ρ ε z| +
            |covariance ρ ε z - hairerCovariance N ρ ε z| := by
          rw [hid]
          simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
            abs_sub (2 * covariance ρ ε z) (covariance ρ ε z - hairerCovariance N ρ ε z)
        _ ≤ 2 * (CQ * torusParabolicSize z ^ (-(1 : ℝ))) + D :=
          add_le_add (mul_le_mul_of_nonneg_left hQz (by norm_num)) hDz
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left hone hD
          linarith
    have hprod := mul_le_mul
      (mul_le_mul hKz' hDz (abs_nonneg _)
        (mul_nonneg hCK (Real.rpow_nonneg hz.le _))) hsum (abs_nonneg _)
      (mul_nonneg (mul_nonneg hCK (Real.rpow_nonneg hz.le _)) hD)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      _ ≤ (CK * torusParabolicSize z ^ (-(3 : ℝ)) * D) *
          ((2 * CQ + D) * torusParabolicSize z ^ (-(1 : ℝ))) := hprod
      _ = A * constantsComparisonSingularWeight 4 z := by
        simp only [constantsComparisonSingularWeight, hz, hs, and_self, ite_true]
        dsimp [A]
        rw [show (CK * torusParabolicSize z ^ (-(3 : ℝ)) * D) *
            ((2 * CQ + D) * torusParabolicSize z ^ (-(1 : ℝ))) =
          CK * D * (2 * CQ + D) * (torusParabolicSize z ^ (-(3 : ℝ)) *
            torusParabolicSize z ^ (-(1 : ℝ))) by ring]
        rw [← Real.rpow_add hz]
        norm_num
  · have hw3 : constantsComparisonSingularWeight 3 z = 0 := by
      simp [constantsComparisonSingularWeight, hs]
    have hw4 : constantsComparisonSingularWeight 4 z = 0 := by
      simp [constantsComparisonSingularWeight, hs]
    have hKzero : hairerKernelTorus N z = 0 :=
      abs_eq_zero.mp (le_antisymm (by simpa [hw3] using hKz) (abs_nonneg _))
    simp [hKzero, hw4]

/-- All four Bochner integrals in the difference of (10.41) exist at every fixed positive scale. -/
theorem constantsComparison_C2_integrability
    (N : ℕ) (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun z : SpaceTime => massiveHeatKernel z * covariance ρ ε z ^ 2) ∧
    Integrable (fun z : SpaceTime => hairerKernelTorus N z * hairerCovariance N ρ ε z ^ 2) ∧
    Integrable (fun z : SpaceTime => constantsComparisonR N z * covariance ρ ε z ^ 2) ∧
    Integrable (fun z : SpaceTime => hairerKernelTorus N z *
      (covariance ρ ε z - hairerCovariance N ρ ε z) *
      (covariance ρ ε z + hairerCovariance N ρ ε z)) := by
  have hQm := (covariance_facts ρ hρ hε).2.1.measurable
  have hKm := measurable_constantsComparison_hairerKernelTorus N
  have hQKm := constantsComparison_hairerCovariance_measurable N ρ hε hρ hε1
  obtain ⟨d₁, hd₁, hdom₁⟩ := constantsComparison_C2_first_majorant N ρ hρ
  obtain ⟨d₂, hd₂, hdom₂⟩ := constantsComparison_C2_second_majorant N ρ hρ
  have hRi : Integrable (fun z : SpaceTime =>
      constantsComparisonR N z * covariance ρ ε z ^ 2) :=
    hd₁.mono' (((measurable_massiveHeatKernel.sub hKm).mul
      (hQm.pow_const 2)).aestronglyMeasurable) (hdom₁ hε hε1)
  have hDi : Integrable (fun z : SpaceTime => hairerKernelTorus N z *
      (covariance ρ ε z - hairerCovariance N ρ ε z) *
      (covariance ρ ε z + hairerCovariance N ρ ε z)) :=
    hd₂.mono' (((hKm.mul (hQm.sub hQKm)).mul
      (hQm.add hQKm)).aestronglyMeasurable) (hdom₂ hε hε1)
  have hGi := (constants_finite ρ hρ ⟨hε, hε1⟩).2.2.2.2.2.2.2
  refine ⟨hGi, ?_, hRi, hDi⟩
  apply (hGi.sub (hRi.add hDi)).congr
  filter_upwards [] with z
  simp only [Pi.sub_apply, Pi.add_apply, constantsComparisonR]
  ring

end RegularityStructures.Phi43

end
