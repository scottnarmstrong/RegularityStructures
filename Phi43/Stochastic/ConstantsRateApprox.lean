/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateModulus
public import Phi43.Stochastic.ConstantsComparisonApproxLp
public import Phi43.Stochastic.ConstantsComparisonConvolution
public import Phi43.Constants.Finite
public import Phi43.Torus.KernelBoundsSupport
public import Phi43.Torus.KernelBoundsConvolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# A quantitative approximate identity

A translation modulus `∫ ‖f(· - h) - f‖ᵖ ≤ C size(h)^γ` for `f ∈ Lᵖ(ℝ × T³)` gives the rate
`∫ ‖ρ_ε^♯ * f - f‖ᵖ ≤ K ε^γ` for every mollifier, by the Hölder (Jensen) inequality for the
probability-like weight `|ρ_ε^♯|`, Tonelli, and the parabolic support bound of `ρ_ε^♯`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

/-- Jensen/Hölder in `ℝ≥0∞`: `(∫ a b)^p ≤ (∫ a)^(p/q) ∫ a b^p`. -/
theorem constantsRate_lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p q : ℝ} (hpq : p.HolderConjugate q) {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ)
    (hb : AEMeasurable b μ) :
    (∫⁻ x, a x * b x ∂μ) ^ p ≤ (∫⁻ x, a x ∂μ) ^ (p / q) * ∫⁻ x, a x * b x ^ p ∂μ := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have hsum : 1 / q + 1 / p = 1 := by
    have := hpq.symm.inv_add_inv_eq_one
    simpa [one_div, add_comm] using this
  have hmul : ∀ x, a x * b x = a x ^ (1 / q) * (a x ^ (1 / p) * b x) := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hsum,
      ENNReal.rpow_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm (f := fun x => a x ^ (1 / q))
    (g := fun x => a x ^ (1 / p) * b x) (ha.pow_const _)
    ((ha.pow_const _).mul hb)
  have h1 : ∫⁻ x, (a x ^ (1 / q)) ^ q ∂μ = ∫⁻ x, a x ∂μ := by
    congr 1
    funext x
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]
  have h2 : ∫⁻ x, (a x ^ (1 / p) * b x) ^ p ∂μ = ∫⁻ x, a x * b x ^ p ∂μ := by
    congr 1
    funext x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  have hH' : ∫⁻ x, a x * b x ∂μ ≤
      (∫⁻ x, a x ∂μ) ^ (1 / q) * (∫⁻ x, a x * b x ^ p ∂μ) ^ (1 / p) := by
    rw [← h1, ← h2]
    exact (lintegral_congr hmul).le.trans hH
  calc
    (∫⁻ x, a x * b x ∂μ) ^ p ≤
        ((∫⁻ x, a x ∂μ) ^ (1 / q) * (∫⁻ x, a x * b x ^ p ∂μ) ^ (1 / p)) ^ p :=
      ENNReal.rpow_le_rpow hH' hp.le
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        one_div p, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one, one_div q, inv_mul_eq_div]

/-- Quantitative approximate identity in `Lᵖ(ℝ × T³)` from a translation modulus. -/
theorem constantsRate_mollify_sub_lintegral_le (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {f : SpaceTime → ℝ} (hmeas : Measurable f) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : MemLp f (ENNReal.ofReal p)) {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hmod : ∀ h : SpaceTime, 0 < torusParabolicSize h →
      ∫⁻ z, ‖f (z - h) - f z‖ₑ ^ p ≤ ENNReal.ofReal (C * torusParabolicSize h ^ γ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫⁻ z, ‖spaceTimeConvolution (periodise ρ ε) f z - f z‖ₑ ^ p ≤
        ENNReal.ofReal (K * ε ^ γ) := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  obtain ⟨B, hB, hsupp⟩ := periodise_support_parabolic_bound ρ hρ
  let Mρ : ℝ := ∫ z : ParabolicSpace, |ρ z|
  have hMρ : 0 ≤ Mρ := integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => abs_nonneg _)
  refine ⟨Mρ ^ p * (C * B ^ γ), by positivity, ?_⟩
  intro ε hε hε1
  set k : SpaceTime → ℝ := periodise ρ ε with hk
  have hkm : Measurable k := measurable_periodise ρ hρ
  have hki : Integrable k := integrable_periodise ρ hρ hε
  have hmass : ∫ z : SpaceTime, k z = 1 := constantsComparison_periodise_mass ρ hρ hε
  have hexists := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hf
  have hint : ∀ z : SpaceTime, Integrable (fun w => k w * f (z - w)) := fun z => hexists z
  -- the mass of `|k|`
  have hm : ∫⁻ w, ‖k w‖ₑ ≤ ENNReal.ofReal Mρ := by
    have h1 : ∫⁻ w, ‖k w‖ₑ = ENNReal.ofReal (∫ w, |k w|) := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hki]
      simp only [Real.norm_eq_abs]
    rw [h1]
    apply ENNReal.ofReal_le_ofReal
    calc
      ∫ w, |k w| ≤ ∫ y : ParabolicSpace, |rescale ρ ε y| := integral_abs_periodise_le ρ hρ hε hε1
      _ = Mρ := integral_abs_rescale ρ hε
  -- pointwise step
  have hpt : ∀ z : SpaceTime, ‖spaceTimeConvolution k f z - f z‖ₑ ≤
      ∫⁻ w, ‖k w‖ₑ * ‖f (z - w) - f z‖ₑ := by
    intro z
    have hid : spaceTimeConvolution k f z - f z = ∫ w, k w * (f (z - w) - f z) := by
      have h1 : ∫ w, k w * (f (z - w) - f z) =
          (∫ w, k w * f (z - w)) - ∫ w, k w * f z := by
        rw [← integral_sub (hint z) (hki.mul_const (f z))]
        congr 1
        funext w
        ring
      rw [h1, integral_mul_const, hmass, one_mul]
      rfl
    rw [hid]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1
    funext w
    rw [enorm_mul]
  have hmeas2 : Measurable (fun x : SpaceTime × SpaceTime =>
      ‖k x.2‖ₑ * ‖f (x.1 - x.2) - f x.1‖ₑ ^ p) := by
    have h1 : Measurable (fun x : SpaceTime × SpaceTime => ‖k x.2‖ₑ) :=
      (hkm.comp measurable_snd).enorm
    have h2 : Measurable (fun x : SpaceTime × SpaceTime => f (x.1 - x.2) - f x.1) :=
      (hmeas.comp (measurable_fst.sub measurable_snd)).sub (hmeas.comp measurable_fst)
    exact h1.mul (h2.enorm.pow_const p)
  have hz : ∀ z : SpaceTime, ‖spaceTimeConvolution k f z - f z‖ₑ ^ p ≤
      (ENNReal.ofReal Mρ) ^ (p / q) *
        ∫⁻ w, ‖k w‖ₑ * ‖f (z - w) - f z‖ₑ ^ p := by
    intro z
    calc
      ‖spaceTimeConvolution k f z - f z‖ₑ ^ p ≤
          (∫⁻ w, ‖k w‖ₑ * ‖f (z - w) - f z‖ₑ) ^ p :=
        ENNReal.rpow_le_rpow (hpt z) hp.le
      _ ≤ (∫⁻ w, ‖k w‖ₑ) ^ (p / q) * ∫⁻ w, ‖k w‖ₑ * ‖f (z - w) - f z‖ₑ ^ p :=
        constantsRate_lintegral_mul_rpow_le volume hpq hkm.enorm.aemeasurable
          (((hmeas.comp (measurable_const.sub measurable_id)).sub measurable_const).enorm
            |>.aemeasurable)
      _ ≤ _ := by
        gcongr
  have hsupport : ∀ᵐ w : SpaceTime ∂volume, ‖k w‖ₑ *
      ∫⁻ z, ‖f (z - w) - f z‖ₑ ^ p ≤
      ‖k w‖ₑ * ENNReal.ofReal (C * (B * ε) ^ γ) := by
    filter_upwards [constantsRate_ae_size_pos] with w hwpos
    by_cases hw : k w = 0
    · simp [hw]
    · apply mul_le_mul_right
      refine (hmod w hwpos).trans (ENNReal.ofReal_le_ofReal ?_)
      have hsz : torusParabolicSize w ≤ B * ε := hsupp hε hε1 w hw
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (torusParabolicSize_nonneg w) hsz hγ) hC
  calc
    ∫⁻ z, ‖spaceTimeConvolution k f z - f z‖ₑ ^ p ≤
        ∫⁻ z, (ENNReal.ofReal Mρ) ^ (p / q) *
          ∫⁻ w, ‖k w‖ₑ * ‖f (z - w) - f z‖ₑ ^ p := lintegral_mono hz
    _ = (ENNReal.ofReal Mρ) ^ (p / q) *
        ∫⁻ z, ∫⁻ w, ‖k w‖ₑ * ‖f (z - w) - f z‖ₑ ^ p := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg
        (div_nonneg hp.le hq.le) ENNReal.ofReal_ne_top)]
    _ = (ENNReal.ofReal Mρ) ^ (p / q) *
        ∫⁻ w, ∫⁻ z, ‖k w‖ₑ * ‖f (z - w) - f z‖ₑ ^ p := by
      rw [lintegral_lintegral_swap hmeas2.aemeasurable]
    _ = (ENNReal.ofReal Mρ) ^ (p / q) *
        ∫⁻ w, ‖k w‖ₑ * ∫⁻ z, ‖f (z - w) - f z‖ₑ ^ p := by
      congr 1
      apply lintegral_congr
      intro w
      rw [lintegral_const_mul']
      exact enorm_ne_top
    _ ≤ (ENNReal.ofReal Mρ) ^ (p / q) *
        ∫⁻ w, ‖k w‖ₑ * ENNReal.ofReal (C * (B * ε) ^ γ) := by
      exact mul_le_mul_right (lintegral_mono_ae hsupport) _
    _ = (ENNReal.ofReal Mρ) ^ (p / q) *
        ((∫⁻ w, ‖k w‖ₑ) * ENNReal.ofReal (C * (B * ε) ^ γ)) := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ (ENNReal.ofReal Mρ) ^ (p / q) *
        (ENNReal.ofReal Mρ * ENNReal.ofReal (C * (B * ε) ^ γ)) := by
      gcongr
    _ = ENNReal.ofReal (Mρ ^ p * (C * B ^ γ) * ε ^ γ) := by
      have hexp : p / q + 1 = p := by rw [hpq.div_conj_eq_sub_one]; ring
      have hpow : (ENNReal.ofReal Mρ) ^ (p / q) * ENNReal.ofReal Mρ =
          ENNReal.ofReal (Mρ ^ p) := by
        calc
          (ENNReal.ofReal Mρ) ^ (p / q) * ENNReal.ofReal Mρ =
              (ENNReal.ofReal Mρ) ^ (p / q) * (ENNReal.ofReal Mρ) ^ (1 : ℝ) := by
            rw [ENNReal.rpow_one]
          _ = (ENNReal.ofReal Mρ) ^ (p / q + 1) :=
            (ENNReal.rpow_add_of_nonneg _ _ (div_nonneg hp.le hq.le) (by norm_num)).symm
          _ = ENNReal.ofReal Mρ ^ p := by rw [hexp]
          _ = ENNReal.ofReal (Mρ ^ p) := (ENNReal.ofReal_rpow_of_nonneg hMρ hp.le)
      rw [← mul_assoc, hpow, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow hB.le hε.le]
      ring

end RegularityStructures.Phi43

end
