/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateSunsetEst

/-!
# A power rate for the sunset-constant comparison

`constantsRate_sunset`: `|C₂^ε - C̃₂^ε - L₂| ≤ C ε^{1/6}` for `ε ∈ (0, 1]`.  There is no logarithmic
obstruction: the cancellation of the logarithmic divergences is carried by the covariance
difference `Q_ε - P_ε = R_ε ⋆ G_ε + K_ε ⋆ R_ε`, which is bounded by Hölder in `L³ × L^{3/2}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_sunset (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C θ' : ℝ, 0 < θ' ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      |sunsetConstant ρ ε - hairerSunsetConstant N ρ ε - constantsComparison_sunsetLimit N| ≤
        C * ε ^ θ' := by
  obtain ⟨cR, hcR, hR⟩ := constantsRate_remainder_rate N ρ hρ
  obtain ⟨cG, hcG, hG⟩ := constantsRate_massive_rate ρ hρ
  obtain ⟨cK, hcK, hK⟩ := constantsRate_hairer_rate N ρ hρ
  obtain ⟨MG, hMG, hUG⟩ := constantsRate_massive_unif ρ hρ
  obtain ⟨MK, hMK, hUK⟩ := constantsRate_hairer_unif N ρ hρ
  obtain ⟨MR, hMR, hUR⟩ := constantsRate_remainder_unif N ρ hρ
  have hRmem : MemLp (constantsComparisonR N) (ENNReal.ofReal 3) := constantsRate_R_memLp N
  have hGmem := constantsRate_massive_memLp
  have hKmem := constantsRate_hairer_memLp N
  set nR : ℝ≥0∞ := eLpNorm (constantsComparisonR N) (ENNReal.ofReal 3) volume with hnR
  set nG : ℝ≥0∞ := eLpNorm massiveHeatKernel (ENNReal.ofReal (3 / 2)) volume with hnG
  set nK : ℝ≥0∞ := eLpNorm (hairerKernelTorus N) (ENNReal.ofReal (3 / 2)) volume with hnK
  have hnRt : nR ≠ ⊤ := hRmem.eLpNorm_lt_top.ne
  have hnGt : nG ≠ ⊤ := hGmem.eLpNorm_lt_top.ne
  have hnKt : nK ≠ ⊤ := hKmem.eLpNorm_lt_top.ne
  let uG : ℝ≥0∞ := ENNReal.ofReal MG * nG
  let uK : ℝ≥0∞ := ENNReal.ofReal MK * nK
  let uR : ℝ≥0∞ := ENNReal.ofReal MR * nR
  have huGt : uG ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hnGt
  have huKt : uK ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hnKt
  have huRt : uR ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hnRt
  let Est : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ := fun aR aG aK =>
    2 * (nR * ((aG * uG + nG * aG) * (uG * uG + nG * nG))) +
      2 * ((aR * uG + nR * aG + (aK * uR + nK * aR)) * (nK * (uG * uG + uK * uK)) +
        (nR * nG + nK * nR) * (nK * ((aG * uG + nG * aG) + (aK * uK + nK * aK))))
  let Cenn : ℝ≥0∞ := Est (ENNReal.ofReal cR) (ENNReal.ofReal cG) (ENNReal.ofReal cK)
  have hCenn : Cenn ≠ ⊤ := by
    simp only [Cenn, Est]
    finiteness
  refine ⟨Cenn.toReal, 1 / 6, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨hε0, hε1⟩ := hε
  set t : ℝ := ε ^ (1 / 6 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hε0.le _
  have ht3 : ε ^ (1 / 3 : ℝ) ≤ t := by
    rw [ht]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
  have haR : eLpNorm (fun z => wickComparisonR N ρ ε z - constantsComparisonR N z)
      (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (cR * t) := by
    simpa [ht] using hR ε hε0 hε1
  have haG : eLpNorm (fun z => mollifiedKernel ρ ε z - massiveHeatKernel z)
      (ENNReal.ofReal (3 / 2)) volume ≤ ENNReal.ofReal (cG * t) :=
    (hG ε hε0 hε1).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ht3 hcG))
  have haK : eLpNorm (fun z => hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z)
      (ENNReal.ofReal (3 / 2)) volume ≤ ENNReal.ofReal (cK * t) :=
    (hK ε hε0 hε1).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ht3 hcK))
  have hest := constantsRate_sunset_estimate N ρ hρ hε0 hε1 haR haG haK (hUG ε hε0 hε1)
    (hUK ε hε0 hε1) (hUR ε hε0 hε1) le_rfl le_rfl le_rfl
    ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top, huGt, huKt, huRt,
      hnRt, hnGt, hnKt⟩
  have hbound : ‖sunsetConstant ρ ε - hairerSunsetConstant N ρ ε -
      constantsComparison_sunsetLimit N‖ₑ ≤ ENNReal.ofReal t * Cenn := by
    refine hest.trans (le_of_eq ?_)
    simp only [Cenn, Est]
    rw [ENNReal.ofReal_mul hcR, ENNReal.ofReal_mul hcG, ENNReal.ofReal_mul hcK]
    ring
  have := constantsRate_enorm_le_real ht0 hCenn hbound
  calc
    _ ≤ t * Cenn.toReal := this
    _ = Cenn.toReal * ε ^ (1 / 6 : ℝ) := by rw [ht]; ring

end RegularityStructures.Phi43

end
