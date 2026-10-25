/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The L1 bound for periodised multiplier kernels

Periodisation cannot increase the L1 norm: Tonelli and the integer translates of `(0,1]` give the
bound directly. This is an internal ingredient of the scale-uniform Fourier multiplier estimate used
in the comparison of the heat and Littlewood--Paley norms.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

private def integerPeriodEquiv : ℤ ≃ AddSubgroup.zmultiples (1 : ℝ) := by
  let f : ℤ → AddSubgroup.zmultiples (1 : ℝ) :=
    fun k => ⟨(k : ℝ), ⟨k, by simp only [zsmul_eq_mul, mul_one]⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro k l h
    have hc : (k : ℝ) = (l : ℝ) := congrArg Subtype.val h
    exact_mod_cast hc
  · intro x
    obtain ⟨k, hk⟩ := x.2
    refine ⟨k, Subtype.ext ?_⟩
    simpa only [zsmul_eq_mul, mul_one] using hk

theorem lintegral_periodise_int_enorm_le (f : ℝ → ℂ) (hf : Continuous f) :
    (∫⁻ x in Ioc (0 : ℝ) 1, ‖∑' k : ℤ, f (x + k)‖ₑ) ≤ ∫⁻ x : ℝ, ‖f x‖ₑ := by
  have hfund : IsAddFundamentalDomain (AddSubgroup.zmultiples (1 : ℝ))
      (Ioc (0 : ℝ) 1) volume := by
    simpa only [zero_add] using
      isAddFundamentalDomain_Ioc (by norm_num : (0 : ℝ) < 1) 0 volume
  have he : (∫⁻ x : ℝ, ‖f x‖ₑ) =
      ∑' k : ℤ, ∫⁻ x in Ioc (0 : ℝ) 1, ‖f (x + k)‖ₑ := by
    rw [hfund.lintegral_eq_tsum'']
    rw [← integerPeriodEquiv.tsum_eq]
    apply tsum_congr
    intro k
    apply lintegral_congr
    intro x
    change ‖f ((k : ℝ) + x)‖ₑ = ‖f (x + (k : ℝ))‖ₑ
    rw [add_comm]
  calc
    _ ≤ ∫⁻ x in Ioc (0 : ℝ) 1, ∑' k : ℤ, ‖f (x + k)‖ₑ :=
      lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0 : ℝ) 1, ‖f (x + k)‖ₑ := by
      apply lintegral_tsum
      intro k
      exact ((hf.comp (continuous_id.add continuous_const)).enorm).measurable.aemeasurable
    _ = _ := he.symm

theorem lintegral_scaled_periodise_int_enorm_le (f : ℝ → ℂ) (hf : Continuous f)
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ x in Ioc (0 : ℝ) 1, ‖∑' k : ℤ, a • f (a * (x + k))‖ₑ) ≤
      ∫⁻ x : ℝ, ‖f x‖ₑ := by
  have hscale : ENNReal.ofReal a • Measure.map (fun x : ℝ => a * x) volume = volume := by
    simpa only [abs_of_pos ha] using Real.smul_map_volume_mul_left ha.ne'
  have hlin : Continuous (fun x : ℝ => a * x) := by fun_prop
  have hscaled : Continuous (fun x : ℝ => a • f (a * x)) :=
    (continuous_const_smul a).comp (hf.comp hlin)
  apply (lintegral_periodise_int_enorm_le (fun x => a • f (a * x)) hscaled).trans_eq
  simp_rw [enorm_smul, Real.enorm_of_nonneg ha.le]
  calc
    _ = ENNReal.ofReal a * ∫⁻ x : ℝ, ‖f (a * x)‖ₑ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal a * ∫⁻ x : ℝ, ‖f x‖ₑ ∂Measure.map (fun x : ℝ => a * x) volume := by
      rw [lintegral_map hf.enorm.measurable (measurable_const_mul a)]
    _ = ∫⁻ x : ℝ, ‖f x‖ₑ ∂(ENNReal.ofReal a • Measure.map (fun x : ℝ => a * x) volume) := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ = _ := by rw [hscale]

end RegularityStructures

end
