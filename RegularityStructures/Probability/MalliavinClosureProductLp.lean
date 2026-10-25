/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCore
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# L² products on a product measure

The white-noise derivative is a function on `Ω × SpaceTime`.  A coefficient depending only on
`Ω` and a deterministic test function depending only on `SpaceTime` have an exactly factorised
L² norm.  This elementary identity is the analytic approximation step used in the closability
argument for the cylindrical Malliavin derivative [HS23, Definition 2.20 and
Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RegularityStructures

theorem memLp_prod_mul_of_memLp_two
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure μ] {f : α → ℝ} {g : β → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) := by
  have hmeas : AEStronglyMeasurable
      (fun p : α × β => f p.1 * g p.2) (μ.prod ν) := by
    exact (hf.aemeasurable.comp_fst).aestronglyMeasurable.mul
      (hg.aemeasurable.comp_snd).aestronglyMeasurable
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas]
  have hleft : AEStronglyMeasurable (fun x : α => ‖f x‖ₑ ^ (2 : ℝ)) μ := by
    exact ((hf.aemeasurable.enorm).pow_const _).aestronglyMeasurable
  have hright : AEStronglyMeasurable (fun y : β => ‖g y‖ₑ ^ (2 : ℝ)) ν := by
    exact ((hg.aemeasurable.enorm).pow_const _).aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat]
  change (∫⁻ p : α × β, ‖f p.1 * g p.2‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) ^ (1 / 2) < ∞
  rw [show (fun p : α × β => ‖f p.1 * g p.2‖ₑ ^ (2 : ℝ)) =
      fun p => (‖f p.1‖ₑ ^ (2 : ℝ)) * (‖g p.2‖ₑ ^ (2 : ℝ)) by
        funext p
        rw [enorm_mul, ← ENNReal.mul_rpow_of_nonneg]
        positivity]
  rw [lintegral_prod_mul hleft.aemeasurable hright.aemeasurable]
  have hfa : (∫⁻ x : α, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) < ∞ := by
    have hpow : (∫⁻ x : α, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) < ∞ := by
      calc
        (∫⁻ x : α, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) =
            eLpNorm f 2 μ := by
          symm
          simpa using (eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
            (f := f) (μ := μ) (by norm_num) (by norm_num) hf.aestronglyMeasurable)
        _ < ∞ := lt_top_iff_ne_top.mpr hf.ne
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hpow
  have hga : (∫⁻ y : β, ‖g y‖ₑ ^ (2 : ℝ) ∂ν) < ∞ := by
    have hpow : (∫⁻ y : β, ‖g y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) < ∞ := by
      calc
        (∫⁻ y : β, ‖g y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) =
            eLpNorm g 2 ν := by
          symm
          simpa using (eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
            (f := g) (μ := ν) (by norm_num) (by norm_num) hg.aestronglyMeasurable)
        _ < ∞ := lt_top_iff_ne_top.mpr hg.ne
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hpow
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).2
    (ENNReal.mul_lt_top hfa hga)

theorem eLpNorm_prod_mul_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure μ] {f : α → ℝ} {g : β → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    eLpNorm (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) =
      eLpNorm f 2 μ * eLpNorm g 2 ν := by
  have hprod : MemLp (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) :=
    memLp_prod_mul_of_memLp_two hf hg
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hprod.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hg.aestronglyMeasurable]
  have hleft : AEStronglyMeasurable (fun x : α => ‖f x‖ₑ ^ (2 : ℝ)) μ := by
    exact ((hf.aemeasurable.enorm).pow_const _).aestronglyMeasurable
  have hright : AEStronglyMeasurable (fun y : β => ‖g y‖ₑ ^ (2 : ℝ)) ν := by
    exact ((hg.aemeasurable.enorm).pow_const _).aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat]
  change (∫⁻ p : α × β, ‖f p.1 * g p.2‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) ^ (1 / 2) =
    (∫⁻ x : α, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2) *
      (∫⁻ y : β, ‖g y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / 2)
  rw [show (fun p : α × β => ‖f p.1 * g p.2‖ₑ ^ (2 : ℝ)) =
      fun p => (‖f p.1‖ₑ ^ (2 : ℝ)) * (‖g p.2‖ₑ ^ (2 : ℝ)) by
        funext p
        rw [enorm_mul, ← ENNReal.mul_rpow_of_nonneg]
        positivity,
    lintegral_prod_mul hleft.aemeasurable hright.aemeasurable]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

end RegularityStructures

end
