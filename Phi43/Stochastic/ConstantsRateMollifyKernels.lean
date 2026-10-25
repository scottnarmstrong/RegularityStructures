/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateMollify
public import Phi43.Stochastic.ConstantsRateModuliKernel
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Rates for the mollified massive, Hairer and remainder kernels

`‖G_ε - G‖_{3/2}` and `‖K_ε - K‖_{3/2}` are `O(ε^{1/3})`, `‖R_ε - R‖₃` is `O(ε^{1/6})`, and the
mollified norms are bounded by a constant multiple of the unmollified ones.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_holder_three_halves : (3 / 2 : ℝ).HolderConjugate 3 := by
  rw [Real.holderConjugate_iff]
  norm_num

theorem constantsRate_holder_three : (3 : ℝ).HolderConjugate (3 / 2) := by
  rw [Real.holderConjugate_iff]
  norm_num

theorem constantsRate_massive_rate (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      eLpNorm (fun z => mollifiedKernel ρ ε z - massiveHeatKernel z)
        (ENNReal.ofReal (3 / 2)) volume ≤ ENNReal.ofReal (c * ε ^ (1 / 3 : ℝ)) := by
  obtain ⟨C, hC, hmod⟩ := constantsRate_massive_modulus
  obtain ⟨c, hc, h⟩ := constantsRate_mollify_eLpNorm_rate ρ hρ measurable_massiveHeatKernel
    constantsRate_holder_three_halves constantsRate_massive_memLp hC (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hmod
  refine ⟨c, hc, fun ε hε hε1 => ?_⟩
  have := h ε hε hε1
  have hγ : (1 / 2 : ℝ) / (3 / 2) = 1 / 3 := by norm_num
  rw [hγ] at this
  simpa only [constantsComparison_mollifiedKernel_eq_convolution ρ] using this

theorem constantsRate_hairer_rate (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      eLpNorm (fun z => hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z)
        (ENNReal.ofReal (3 / 2)) volume ≤ ENNReal.ofReal (c * ε ^ (1 / 3 : ℝ)) := by
  obtain ⟨C, hC, hmod⟩ := constantsRate_hairer_modulus N
  obtain ⟨c, hc, h⟩ := constantsRate_mollify_eLpNorm_rate ρ hρ
    (measurable_constantsComparison_hairerKernelTorus N)
    constantsRate_holder_three_halves (constantsRate_hairer_memLp N) hC
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hmod
  refine ⟨c, hc, fun ε hε hε1 => ?_⟩
  have := h ε hε hε1
  have hγ : (1 / 2 : ℝ) / (3 / 2) = 1 / 3 := by norm_num
  rw [hγ] at this
  simpa only [constantsComparison_hairerMollifiedKernel_eq_convolution N ρ] using this

theorem constantsRate_conv_remainder (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    spaceTimeConvolution (periodise ρ ε) (constantsComparisonR N) = wickComparisonR N ρ ε := by
  have hG := constantsComparison_periodise_convolution_exists ρ hρ hε
    constantsRate_holder_three_halves constantsRate_massive_memLp
  have hK := constantsComparison_periodise_convolution_exists ρ hρ hε
    constantsRate_holder_three_halves (constantsRate_hairer_memLp N)
  funext z
  have h1 : spaceTimeConvolution (periodise ρ ε) (constantsComparisonR N) z =
      spaceTimeConvolution (periodise ρ ε) massiveHeatKernel z -
        spaceTimeConvolution (periodise ρ ε) (hairerKernelTorus N) z := by
    have e := integral_sub (hG z) (hK z)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] at e
    unfold spaceTimeConvolution
    rw [← e]
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [constantsComparisonR_def]
    ring
  rw [h1, constantsComparison_mollifiedKernel_eq_convolution ρ,
    constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
  rfl

theorem constantsRate_measurable_remainder (N : ℕ) : Measurable (constantsComparisonR N) :=
  measurable_massiveHeatKernel.sub (measurable_constantsComparison_hairerKernelTorus N)

theorem constantsRate_remainder_rate (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      eLpNorm (fun z => wickComparisonR N ρ ε z - constantsComparisonR N z)
        (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (c * ε ^ (1 / 6 : ℝ)) := by
  obtain ⟨C, hC, hmod⟩ := constantsRate_R_modulus N
  obtain ⟨c, hc, h⟩ := constantsRate_mollify_eLpNorm_rate ρ hρ
    (f := constantsComparisonR N) (constantsRate_measurable_remainder N)
    constantsRate_holder_three (constantsRate_R_memLp N) hC (by norm_num : (0 : ℝ) ≤ 1 / 2) hmod
  refine ⟨c, hc, fun ε hε hε1 => ?_⟩
  have := h ε hε hε1
  have hγ : (1 / 2 : ℝ) / 3 = 1 / 6 := by norm_num
  rw [hγ] at this
  simpa only [constantsRate_conv_remainder N ρ hρ hε] using this

theorem constantsRate_massive_unif (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      eLpNorm (mollifiedKernel ρ ε) (ENNReal.ofReal (3 / 2)) volume ≤
        ENNReal.ofReal M * eLpNorm massiveHeatKernel (ENNReal.ofReal (3 / 2)) volume := by
  obtain ⟨M, hM, h⟩ := constantsRate_mollify_eLpNorm_le ρ hρ measurable_massiveHeatKernel
    constantsRate_holder_three_halves constantsRate_massive_memLp
  refine ⟨M, hM, fun ε hε hε1 => ?_⟩
  have := h ε hε hε1
  rwa [constantsComparison_mollifiedKernel_eq_convolution ρ] at this

theorem constantsRate_hairer_unif (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      eLpNorm (hairerMollifiedKernel N ρ ε) (ENNReal.ofReal (3 / 2)) volume ≤
        ENNReal.ofReal M * eLpNorm (hairerKernelTorus N) (ENNReal.ofReal (3 / 2)) volume := by
  obtain ⟨M, hM, h⟩ := constantsRate_mollify_eLpNorm_le ρ hρ
    (measurable_constantsComparison_hairerKernelTorus N)
    constantsRate_holder_three_halves (constantsRate_hairer_memLp N)
  refine ⟨M, hM, fun ε hε hε1 => ?_⟩
  have := h ε hε hε1
  rwa [constantsComparison_hairerMollifiedKernel_eq_convolution N ρ] at this

theorem constantsRate_remainder_unif (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      eLpNorm (wickComparisonR N ρ ε) (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal M * eLpNorm (constantsComparisonR N) (ENNReal.ofReal 3) volume := by
  obtain ⟨M, hM, h⟩ := constantsRate_mollify_eLpNorm_le ρ hρ
    (f := constantsComparisonR N) (constantsRate_measurable_remainder N)
    constantsRate_holder_three (constantsRate_R_memLp N)
  refine ⟨M, hM, fun ε hε hε1 => ?_⟩
  have := h ε hε hε1
  rwa [constantsRate_conv_remainder N ρ hρ hε] at this

end RegularityStructures.Phi43

end
