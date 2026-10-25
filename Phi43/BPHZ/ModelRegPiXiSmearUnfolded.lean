/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiXiSmear

/-!
# Smeared periodised semigroup kernel versus the kernel (unfolded)

`∫ (ψ ⋆ ρ_ε^♯ - ψ)² ≤ C ε^a lam^(-(5 + a))` for `ψ = q^♯_t(x, ·)`, `a ∈ [0, 1]`
(`noiseSmearedTest_semigroupPeriodised_sub_sq_integral_le`).  The proof combines the shift-square
integral of the periodised kernel with the fractional parabolic moment of the rescaled mollifier.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem lam_pow_eq {l a : ℝ} (hl : 0 < l) :
    (l ^ 5)⁻¹ * l⁻¹ ^ a = l ^ (-(5 + a)) := by
  rw [Real.rpow_neg hl.le, Real.rpow_add hl, Real.inv_rpow hl.le]
  have : l ^ (5 : ℝ) = l ^ 5 := by norm_cast
  rw [this, mul_inv]

/-- **Smeared periodised semigroup kernel versus the kernel.** -/
theorem noiseSmearedTest_semigroupPeriodised_sub_sq_integral_le {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      ∫ u, (noiseSmearedTest ρ ε (semigroupPeriodised t x) u - semigroupPeriodised t x u) ^ 2 ≤
        C * ε ^ a * (t ^ (1 / 4 : ℝ)) ^ (-(5 + a)) := by
  obtain ⟨c, hc0, hc⟩ := exists_integral_sq_semigroupPeriodised_add_sub_le ha0 ha1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  set Mρ : ℝ := ∫ z : ParabolicSpace, |ρ z| with hMρ
  set Nρ : ℝ := ∫ y : ParabolicSpace, |ρ y| * parabolicNorm y ^ a with hNρ
  have hMρ0 : 0 ≤ Mρ := integral_nonneg fun z => abs_nonneg _
  have hNρ0 : 0 ≤ Nρ :=
    integral_nonneg fun y => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  refine ⟨Mρ * (c * Nρ), by positivity, ?_⟩
  intro ε hε t ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  set lam := t ^ (1 / 4 : ℝ) with hlamdef
  set Λ : ℝ := (lam ^ 5)⁻¹ * lam⁻¹ ^ a with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set ψ := semigroupPeriodised t x with hψ
  have h := hB ht ht1 x
  have hψm : Measurable ψ := h.measurable
  have hψ2 : Integrable (fun w => ψ w ^ 2) := integrable_semigroupPeriodised_sq ht ht1 x
  have hψb : ∀ w, |ψ w| ≤ B * (lam ^ 5)⁻¹ := fun w => h.abs_le w
  have hK1 : ∫ w, periodise ρ ε w = 1 := integral_periodise_eq_one ρ hρ hε.1
  obtain ⟨hKD, hle⟩ := noise_mollify_sub_sq_integral_le (measurable_periodise ρ hρ)
    (integrable_periodise ρ hρ hε.1) hK1 hψm hψb hψ2
  set D : SpaceTime → ℝ := fun s => ∫ u, (ψ (u + s) - ψ u) ^ 2 with hD
  have hD0 : ∀ s, 0 ≤ D s := fun s => integral_nonneg fun u => sq_nonneg _
  have hFm : Measurable (fun p : SpaceTime × SpaceTime => (ψ (p.2 + p.1) - ψ p.2) ^ 2) :=
    ((hψm.comp (measurable_snd.add measurable_fst)).sub (hψm.comp measurable_snd)).pow_const 2
  have hDm : Measurable D := hFm.stronglyMeasurable.integral_prod_right'.measurable
  have hDpt : ∀ y : ParabolicSpace, D (y.1, torusProj y.2) ≤ c * Λ * parabolicNorm y ^ a :=
    fun y => hc ht ht1 x y
  have hResInt := integrable_abs_rescale_mul_parabolicNorm_rpow ρ hρ hε.1 ha0
  have hunf := noise_lintegral_periodise_mul_le ρ hρ hε.1 hε.2
    (fun s => ENNReal.ofReal (D s)) hDm.ennreal_ofReal
  have hI : ∫ s, |periodise ρ ε s| * D s ≤ c * Λ * (ε ^ a * Nρ) := by
    have h1 : ∫ s, |periodise ρ ε s| * D s =
        (∫⁻ s, ENNReal.ofReal (|periodise ρ ε s| * D s)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun s =>
        mul_nonneg (abs_nonneg _) (hD0 s)) hKD.aestronglyMeasurable
    have h2 : ∫⁻ s, ENNReal.ofReal (|periodise ρ ε s| * D s) ≤
        ∫⁻ y : ParabolicSpace, ENNReal.ofReal (c * Λ *
          (|rescale ρ ε y| * parabolicNorm y ^ a)) := by
      calc ∫⁻ s, ENNReal.ofReal (|periodise ρ ε s| * D s)
          = ∫⁻ s, ENNReal.ofReal |periodise ρ ε s| * ENNReal.ofReal (D s) := by
            refine lintegral_congr fun s => ?_
            rw [ENNReal.ofReal_mul (abs_nonneg _)]
        _ ≤ ∫⁻ y : ParabolicSpace, ENNReal.ofReal |rescale ρ ε y| *
              ENNReal.ofReal (D (y.1, torusProj y.2)) := hunf
        _ ≤ _ := by
            refine lintegral_mono fun y => ?_
            rw [← ENNReal.ofReal_mul (abs_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            calc |rescale ρ ε y| * D (y.1, torusProj y.2)
                ≤ |rescale ρ ε y| * (c * Λ * parabolicNorm y ^ a) :=
                  mul_le_mul_of_nonneg_left (hDpt y) (abs_nonneg _)
              _ = _ := by ring
    have h3 : ∫⁻ y : ParabolicSpace, ENNReal.ofReal (c * Λ *
        (|rescale ρ ε y| * parabolicNorm y ^ a)) =
        ENNReal.ofReal (∫ y, c * Λ * (|rescale ρ ε y| * parabolicNorm y ^ a)) :=
      (ofReal_integral_eq_lintegral_ofReal (hResInt.const_mul _)
        (Filter.Eventually.of_forall fun y => mul_nonneg (mul_nonneg hc0 hΛ0)
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (parabolicNorm_nonneg _) _)))).symm
    have h4 : ∫ y, c * Λ * (|rescale ρ ε y| * parabolicNorm y ^ a) =
        c * Λ * (ε ^ a * Nρ) := by
      rw [integral_const_mul, integral_abs_rescale_mul_parabolicNorm_rpow ρ hε.1 a]
    rw [h1]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (h2.trans_eq h3)).trans ?_
    have hnn : 0 ≤ ∫ y, c * Λ * (|rescale ρ ε y| * parabolicNorm y ^ a) := by
      rw [h4]
      exact mul_nonneg (mul_nonneg hc0 hΛ0) (mul_nonneg (Real.rpow_nonneg hε.1.le _) hNρ0)
    rw [ENNReal.toReal_ofReal hnn, h4]
  have hM : ∫ z : SpaceTime, |periodise ρ ε z| ≤ Mρ := integral_abs_periodise_le_integral_abs hρ hε
  rw [← hlamdef, ← lam_pow_eq hlam] at *
  calc ∫ u, (noiseSmearedTest ρ ε ψ u - ψ u) ^ 2
      ≤ (∫ z : SpaceTime, |periodise ρ ε z|) * ∫ s, |periodise ρ ε s| * D s := hle
    _ ≤ Mρ * (c * Λ * (ε ^ a * Nρ)) := by
        apply mul_le_mul hM hI (integral_nonneg fun s => mul_nonneg (abs_nonneg _) (hD0 s)) hMρ0
    _ = _ := by rw [hΛ]; ring

end RegularityStructures.Phi43

end
