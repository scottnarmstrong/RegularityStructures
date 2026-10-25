/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KolmogorovHolderBesovHeat
public import RegularityStructures.PDE.Semigroup
public import RegularityStructures.Torus.HeatKernelIntegrability
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Heat-kernel Hölder bounds on the torus

This file proves the (L^p)-to-(L^\infty) estimate used in the dyadic Kolmogorov
argument.  The pointwise heat-kernel majorant is the periodised Gaussian estimate in
`KolmogorovHolderBesovHeat`; the normalization is the one in Hairer [Hai14, (2.1)--(2.3)].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

open PDE

/-- The scale-free constant in the periodised Gaussian estimate. -/
noncomputable def heatKernelScaleConstant : ℝ :=
  (4 * Real.pi) ^ (-(3 : ℝ) / 2) * gaussianVectorMajorantConstant

theorem heatKernelScaleConstant_nonneg : 0 ≤ heatKernelScaleConstant := by
  unfold heatKernelScaleConstant
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    gaussianVectorMajorantConstant_nonneg

private theorem rpow_le_rpow_mul_of_nonneg_le {a b q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hq : 1 ≤ q) : a ^ q ≤ b ^ (q - 1) * a := by
  calc
    a ^ q = a ^ ((q - 1) + 1) := by congr 1; ring
    _ = a ^ (q - 1) * a ^ (1 : ℝ) :=
      Real.rpow_add_of_nonneg ha (sub_nonneg.mpr hq) (by norm_num)
    _ ≤ b ^ (q - 1) * a ^ (1 : ℝ) := by
      gcongr
    _ = b ^ (q - 1) * a := by simp

theorem heatKernel_rpow_integral_le {p q s : ℝ} (hpq : p.HolderConjugate q)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    ∫ y : Torus3, (heatKernel s y) ^ q ≤
      (heatKernelScaleConstant * s ^ (-(3 : ℝ) / 2)) ^ (q - 1) := by
  let M : ℝ := heatKernelScaleConstant * s ^ (-(3 : ℝ) / 2)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg heatKernelScaleConstant_nonneg (Real.rpow_nonneg hs.le _)
  have hk_le : ∀ y : Torus3, heatKernel s y ≤ M := by
    intro y
    exact heatKernel_le_scale_uniform hs hs1 y
  have hk_nonneg : ∀ y : Torus3, 0 ≤ heatKernel s y := heatKernel_nonneg hs
  have hq : 1 ≤ q := hpq.symm.lt.le
  have hcont : Continuous (fun y : Torus3 => (heatKernel s y) ^ q) := by
    exact (continuous_heatKernel_fixed hs).rpow_const fun _ => Or.inr (zero_le_one.trans hq)
  have hbound : ∀ y : Torus3, |(heatKernel s y) ^ q| ≤ M ^ q := by
    intro y
    rw [abs_of_nonneg (Real.rpow_nonneg (hk_nonneg y) _)]
    exact Real.rpow_le_rpow (hk_nonneg y) (hk_le y) (zero_le_one.trans hq)
  have hpow_int : Integrable (fun y : Torus3 => (heatKernel s y) ^ q) := by
    exact Integrable.of_bound hcont.aestronglyMeasurable (M ^ q)
      (Filter.Eventually.of_forall hbound)
  have hkernel_int : Integrable (heatKernel s) := integrable_heatKernel_fixed hs
  have hmul_int : Integrable (fun y : Torus3 => M ^ (q - 1) * heatKernel s y) :=
    hkernel_int.const_mul _
  have hpoint : ∀ᵐ y ∂(volume : Measure Torus3),
      (heatKernel s y) ^ q ≤ M ^ (q - 1) * heatKernel s y :=
    Filter.Eventually.of_forall fun y =>
      rpow_le_rpow_mul_of_nonneg_le (hk_nonneg y) (hk_le y) hq
  have hintergral :
      ∫ y : Torus3, (heatKernel s y) ^ q ≤
        ∫ y : Torus3, M ^ (q - 1) * heatKernel s y :=
    integral_mono_ae hpow_int hmul_int hpoint
  calc
    ∫ y : Torus3, (heatKernel s y) ^ q ≤
        ∫ y : Torus3, M ^ (q - 1) * heatKernel s y := hintergral
    _ = M ^ (q - 1) * ∫ y : Torus3, heatKernel s y :=
      integral_const_mul _ _
    _ = M ^ (q - 1) := by rw [integral_heatKernel hs]; simp
    _ = (heatKernelScaleConstant * s ^ (-(3 : ℝ) / 2)) ^ (q - 1) := rfl

theorem heatKernel_Lq_norm_le {p q s : ℝ} (hpq : p.HolderConjugate q)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    (∫ y : Torus3, (heatKernel s y) ^ q) ^ (1 / q) ≤
      (heatKernelScaleConstant * s ^ (-(3 : ℝ) / 2)) ^ (1 / p) := by
  have hq : 0 ≤ (1 / q : ℝ) := le_of_lt (one_div_pos.mpr hpq.symm.pos)
  have hnonneg : 0 ≤ ∫ y : Torus3, (heatKernel s y) ^ q := by
    apply integral_nonneg_of_ae
    filter_upwards [] with y
    exact Real.rpow_nonneg (heatKernel_nonneg hs y) _
  have hpow := Real.rpow_le_rpow hnonneg
    (heatKernel_rpow_integral_le hpq hs hs1) hq
  have hM : 0 ≤ heatKernelScaleConstant * s ^ (-(3 : ℝ) / 2) :=
    mul_nonneg heatKernelScaleConstant_nonneg (Real.rpow_nonneg hs.le _)
  rw [← Real.rpow_mul hM] at hpow
  have hexp : (q - 1) * (1 / q) = 1 / p := by
    field_simp [hpq.ne_zero, hpq.symm.ne_zero]
    linear_combination hpq.sub_one_mul_conj
  rw [hexp] at hpow
  exact hpow

theorem heatSemigroup_Lp_to_Linfty {p q s : ℝ} (hpq : p.HolderConjugate q)
    (hs : 0 < s) (hs1 : s ≤ 1) (g : C(Torus3, ℝ)) (x : Torus3) :
    |heatSemigroup s g x| ≤
      (heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)) ^ (1 / p) *
        (∫ y : Torus3, |heatSemigroup (s / 2) g (x - y)| ^ p) ^ (1 / p) := by
  have hs2 : 0 < s / 2 := by linarith
  have hs21 : s / 2 ≤ 1 := by linarith
  let H : C(Torus3, ℝ) := heatOp (s / 2) g
  have hsem : heatSemigroup (s / 2) H x = heatSemigroup s g x := by
    dsimp [H]
    rw [heatSemigroup_heatOp hs2 hs2 g x]
    congr 1
    ring
  have hk : MemLp (heatKernel (s / 2)) (ENNReal.ofReal q) := by
    refine MemLp.of_bound (continuous_heatKernel_fixed hs2).aestronglyMeasurable
      (heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)) ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hs2 y)]
    exact heatKernel_le_scale_uniform hs2 hs21 y
  have hkernel := heatKernel_Lq_norm_le hpq hs2 hs21
  have hsemint := heatSemigroup_eq_torus_integral hs2 H x
  have hHshift : MemLp (fun y : Torus3 => H (x - y)) (ENNReal.ofReal p) := by
    refine MemLp.of_bound
      (H.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ‖H‖ ?_
    exact Filter.Eventually.of_forall fun y => H.norm_coe_le_norm (x - y)
  have hholder := integral_mul_norm_le_Lp_mul_Lq hpq hHshift hk
  have hkernel' :
      (∫ y : Torus3, ‖heatKernel (s / 2) y‖ ^ q) ^ (1 / q) ≤
        (heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)) ^ (1 / p) := by
    convert hkernel using 1
    apply congrArg (fun z : ℝ => z ^ (1 / q))
    apply integral_congr_ae
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hs2 y)]
  calc
    |heatSemigroup s g x| = |heatSemigroup (s / 2) H x| := by rw [hsem]
    _ = |∫ y : Torus3, heatKernel (s / 2) y * H (x - y)| := by rw [hsemint]
    _ ≤ ∫ y : Torus3, ‖heatKernel (s / 2) y * H (x - y)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun y : Torus3 =>
          heatKernel (s / 2) y * H (x - y)))
    _ = ∫ y : Torus3, ‖H (x - y)‖ * ‖heatKernel (s / 2) y‖ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_mul]
      ring
    _ ≤ (∫ y : Torus3, ‖H (x - y)‖ ^ p) ^ (1 / p) *
        (∫ y : Torus3, ‖heatKernel (s / 2) y‖ ^ q) ^ (1 / q) := by
      simpa using hholder
    _ ≤ (∫ y : Torus3, ‖H (x - y)‖ ^ p) ^ (1 / p) *
        (heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)) ^ (1 / p) := by
      exact mul_le_mul_of_nonneg_left hkernel' (Real.rpow_nonneg (by positivity) _)
    _ = (heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)) ^ (1 / p) *
        (∫ y : Torus3, |heatSemigroup (s / 2) g (x - y)| ^ p) ^ (1 / p) := by
      rw [mul_comm]
      congr 1
      apply congrArg (fun z : ℝ => z ^ (1 / p))
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp [H]
      rw [← heatOp_eq_heatSemigroup hs2]

theorem heatSemigroup_Lp_to_Linfty_global {p q s : ℝ} (hpq : p.HolderConjugate q)
    (hs : 0 < s) (hs1 : s ≤ 1) (g : C(Torus3, ℝ)) (x : Torus3) :
    |heatSemigroup s g x| ≤
      (heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)) ^ (1 / p) *
        (∫ y : Torus3, |heatSemigroup (s / 2) g y| ^ p) ^ (1 / p) := by
  have h := heatSemigroup_Lp_to_Linfty hpq hs hs1 g x
  rw [integral_sub_left_eq_self (fun y : Torus3 =>
    |heatSemigroup (s / 2) g y| ^ p) (volume : Measure Torus3) x] at h
  exact h

theorem heatSemigroup_norm_pow_le {p : ℕ} {q s : ℝ}
    (hpq : (p : ℝ).HolderConjugate q) (hs : 0 < s) (hs1 : s ≤ 1)
    (g : C(Torus3, ℝ)) :
    ‖heatOp s g‖ ^ p ≤
      (heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)) *
        ∫ y : Torus3, |heatSemigroup (s / 2) g y| ^ (p : ℝ) := by
  have hp0 : p ≠ 0 := by
    intro hp
    subst p
    exact (not_lt_of_ge (by norm_num)) hpq.lt
  let M : ℝ := heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)
  let I : ℝ := ∫ y : Torus3, |heatSemigroup (s / 2) g y| ^ (p : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg heatKernelScaleConstant_nonneg (Real.rpow_nonneg (by linarith) _)
  have hI : 0 ≤ I := by
    dsimp [I]
    apply integral_nonneg_of_ae
    filter_upwards [] with y
    positivity
  have hpoint : ∀ x : Torus3, ‖heatOp s g x‖ ^ p ≤ M * I := by
    intro x
    have hx0 := heatSemigroup_Lp_to_Linfty_global hpq hs hs1 g x
    have hx : |heatOp s g x| ≤
        M ^ (1 / (p : ℝ)) * I ^ (1 / (p : ℝ)) := by
      rw [heatOp_eq_heatSemigroup hs]
      simpa [M, I] using hx0
    have hpw := pow_le_pow_left₀ (abs_nonneg _) hx p
    calc
      |heatOp s g x| ^ p ≤
          (M ^ (1 / (p : ℝ)) * I ^ (1 / (p : ℝ))) ^ p := by
        simpa [M, I] using hpw
      _ = M * I := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hM,
          ← Real.rpow_natCast, ← Real.rpow_mul hI]
        have hpi : (1 / (p : ℝ)) * (p : ℝ) = 1 := by
          field_simp
        rw [hpi, Real.rpow_one, Real.rpow_one]
  calc
    ‖heatOp s g‖ ^ p =
        (⨆ x : Torus3, ‖heatOp s g x‖) ^ p := by
          rw [ContinuousMap.norm_eq_iSup_norm]
    _ = ⨆ x : Torus3, ‖heatOp s g x‖ ^ p := by
      apply Real.iSup_pow
      intro x
      exact norm_nonneg _
    _ ≤ M * I := by
      exact ciSup_le hpoint
    _ = (heatKernelScaleConstant * (s / 2) ^ (-(3 : ℝ) / 2)) *
        ∫ y : Torus3, |heatSemigroup (s / 2) g y| ^ (p : ℝ) := by rfl

end RegularityStructures

end
