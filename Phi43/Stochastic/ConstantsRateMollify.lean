/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateApprox
public import Phi43.Stochastic.ConstantsRateCorr
public import Phi43.Stochastic.ConstantsRateModuliR
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import Phi43.Stochastic.ConstantsComparisonKernelMemLp
public import Phi43.Constants.Finite
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Rates for the mollified kernels in `Lᵖ`

From the translation moduli: `‖G_ε - G‖_{3/2}`, `‖K_ε - K‖_{3/2}` are `O(ε^{1/3})` and
`‖R_ε - R‖₃` is `O(ε^{1/6})`, uniformly bounded norms of the mollified kernels, and the identity
`R_ε = ρ_ε^♯ * R`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_convolution_aestronglyMeasurable (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} {g : SpaceTime → ℝ} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (spaceTimeConvolution (periodise ρ ε) g) volume := by
  change AEStronglyMeasurable
    (MeasureTheory.convolution (periodise ρ ε) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume
  exact (measurable_periodise ρ hρ).aestronglyMeasurable.convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hg

theorem constantsRate_eLpNorm_le_of_lintegral_le {g : SpaceTime → ℝ}
    (hg : AEStronglyMeasurable g volume) {p K γ ε : ℝ} (hp : 0 < p) (hK : 0 ≤ K) (hε : 0 < ε)
    (h : ∫⁻ z, ‖g z‖ₑ ^ p ≤ ENNReal.ofReal (K * ε ^ γ)) :
    eLpNorm g (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (K ^ (1 / p) * ε ^ (γ / p)) := by
  rw [constantsRate_eLpNorm_eq hg hp]
  calc
    (∫⁻ z, ‖g z‖ₑ ^ p) ^ (1 / p) ≤ (ENNReal.ofReal (K * ε ^ γ)) ^ (1 / p) :=
      ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal ((K * ε ^ γ) ^ (1 / p)) :=
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
    _ = ENNReal.ofReal (K ^ (1 / p) * ε ^ (γ / p)) := by
      congr 1
      rw [Real.mul_rpow hK (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
      congr 2
      ring

theorem constantsRate_mollify_eLpNorm_rate (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {f : SpaceTime → ℝ} (hmeas : Measurable f) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : MemLp f (ENNReal.ofReal p)) {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hmod : ∀ h : SpaceTime, 0 < torusParabolicSize h →
      ∫⁻ z, ‖f (z - h) - f z‖ₑ ^ p ≤ ENNReal.ofReal (C * torusParabolicSize h ^ γ)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      eLpNorm (fun z => spaceTimeConvolution (periodise ρ ε) f z - f z) (ENNReal.ofReal p)
        volume ≤ ENNReal.ofReal (c * ε ^ (γ / p)) := by
  have hp : 0 < p := hpq.pos
  obtain ⟨K, hK, hKε⟩ := constantsRate_mollify_sub_lintegral_le ρ hρ hmeas hpq hf hC hγ hmod
  refine ⟨K ^ (1 / p), by positivity, ?_⟩
  intro ε hε hε1
  have hcm := constantsRate_convolution_aestronglyMeasurable ρ hρ (ε := ε) hmeas.aestronglyMeasurable
  exact constantsRate_eLpNorm_le_of_lintegral_le (hcm.sub hmeas.aestronglyMeasurable) hp hK hε
    (hKε ε hε hε1)

theorem constantsRate_mollify_eLpNorm_le (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {f : SpaceTime → ℝ} (hmeas : Measurable f) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : MemLp f (ENNReal.ofReal p)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      eLpNorm (spaceTimeConvolution (periodise ρ ε) f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) volume := by
  refine ⟨∫ z : ParabolicSpace, |ρ z|, integral_nonneg (fun z => abs_nonneg _), ?_⟩
  intro ε hε hε1
  have hki := integrable_periodise ρ hρ hε
  have hmass : 0 < ∫ y : SpaceTime, |periodise ρ ε y| := by
    have habs := abs_integral_le_integral_abs (f := periodise ρ ε)
      (μ := (volume : Measure SpaceTime))
    rw [constantsComparison_periodise_mass ρ hρ hε] at habs
    exact lt_of_lt_of_le zero_lt_one (by simpa using habs)
  have hconv := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hf
  have h := constantsComparison_spaceTimeConvolution_eLpNorm_le (k := periodise ρ ε) (f := f)
    hpq (measurable_periodise ρ hρ) hki hmeas hmass
    (Filter.Eventually.of_forall (fun x => hconv x)) hf
  have hmassle : ∫ y : SpaceTime, |periodise ρ ε y| ≤ ∫ z : ParabolicSpace, |ρ z| := by
    calc
      ∫ y : SpaceTime, |periodise ρ ε y| ≤ ∫ z : ParabolicSpace, |rescale ρ ε z| :=
        integral_abs_periodise_le ρ hρ hε hε1
      _ = ∫ z : ParabolicSpace, |ρ z| := integral_abs_rescale ρ hε
  refine h.trans ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hmassle) le_rfl

end RegularityStructures.Phi43

end
