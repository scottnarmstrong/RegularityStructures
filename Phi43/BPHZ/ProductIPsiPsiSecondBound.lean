/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondDomination
public import Phi43.BPHZ.ProductIPsiPsiSecondFieldFubini
import Mathlib.Tactic

/-!
# Second moment of `Q_t Π_x I(Ψ)Ψ (x)`

`hairerIPsiPsiField_semigroup_second_moment_le`: for `κ ∈ (0, 1/16)`, `t ∈ (0, 1]`, uniformly in
`ε ∈ (0, 1]` and `x`,
`E |∫ Q_t(x, y) Π_x I(Ψ)Ψ (y) dy|² ≤ C (t^(1/4))^(2 (1 - 2κ) + κ)`.

Proof: Fubini (`hairerIPsiPsiField_integral_sq_eq`), the pointwise covariance majorant
(`ipsi_tested_cov_dominated`), periodisation of the `ℝ⁴ × ℝ⁴` integral against the weighted
semigroup test profile (`ipsiWeighted_integral_comp_proj`) and the profile double bounds.
With `θ = κ/2`, `γ = 1 - κ/2`, `δ = κ` the two terms are `lam^(2-2κ)` and `lam^(2-κ)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The `ℝ⁴ × ℝ⁴` integral of the two majorant terms, from the profile double bounds. -/
theorem ipsi_majorant_integral_le {θ : ℝ} (hθ : 0 < θ) (hθ5 : θ < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      Integrable (fun q : ParabolicSpace × ParabolicSpace => ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-θ)) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-θ)))) ∧
      ∫ q : ParabolicSpace × ParabolicSpace, ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-θ)) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-θ))) ≤
        K * (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ)) := by
  obtain ⟨K, hK, hD⟩ := ipsiWeighted_doubleBound_theta hθ hθ5
  refine ⟨K, hK, fun {t} ht ht1 x => ?_⟩
  have h := hD ht ht1 x
  have hI : Integrable (fun w : SpaceTime × SpaceTime => ipsiWeightedPeriodised t x w.1 *
      ipsiWeightedPeriodised t x w.2 * ((1 + torusParabolicSize (w.1 - spaceTimeProj x) ^ (-θ)) *
        (1 + torusParabolicSize (w.2 - spaceTimeProj x) ^ (-θ)))) := by
    have := h.1
    simpa only [ipsiWeightedPeriodised_abs] using this
  have hm : Measurable (fun w : SpaceTime × SpaceTime =>
      (1 + torusParabolicSize (w.1 - spaceTimeProj x) ^ (-θ)) *
        (1 + torusParabolicSize (w.2 - spaceTimeProj x) ^ (-θ))) := by
    have m1 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.1 - spaceTimeProj x) ^ (-θ)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_const)).pow_const _)
    have m2 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.2 - spaceTimeProj x) ^ (-θ)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_const)).pow_const _)
    exact (measurable_const.add m1).mul (measurable_const.add m2)
  have hnn : ∀ u v : SpaceTime, 0 ≤ (1 + torusParabolicSize (u - spaceTimeProj x) ^ (-θ)) *
      (1 + torusParabolicSize (v - spaceTimeProj x) ^ (-θ)) := fun u v => by
    have a1 := Real.rpow_nonneg (torusParabolicSize_nonneg (u - spaceTimeProj x)) (-θ)
    have a2 := Real.rpow_nonneg (torusParabolicSize_nonneg (v - spaceTimeProj x)) (-θ)
    positivity
  obtain ⟨hi, he⟩ := ipsiWeighted_integral_comp_proj ht ht1 x
    (Θ := fun u v => (1 + torusParabolicSize (u - spaceTimeProj x) ^ (-θ)) *
      (1 + torusParabolicSize (v - spaceTimeProj x) ^ (-θ))) hm hnn hI
  refine ⟨hi, ?_⟩
  rw [he]
  have := h.2
  simpa only [ipsiWeightedPeriodised_abs] using this

theorem ipsi_majorant_integral_inv_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      Integrable (fun q : ParabolicSpace × ParabolicSpace => ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ))) ∧
      ∫ q : ParabolicSpace × ParabolicSpace, ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ)) ≤
        K * (t ^ (1 / 4 : ℝ)) ^ (-(1 : ℝ)) := by
  obtain ⟨K, hK, hD⟩ := ipsiWeighted_doubleBound_inv (e := 1) (by norm_num)
  refine ⟨K, hK, fun {t} ht ht1 x => ?_⟩
  have h := hD ht ht1 x
  have hI : Integrable (fun w : SpaceTime × SpaceTime => ipsiWeightedPeriodised t x w.1 *
      ipsiWeightedPeriodised t x w.2 * torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ))) := by
    have := h.1
    simpa only [ipsiWeightedPeriodised_abs] using this
  have hm : Measurable (fun w : SpaceTime × SpaceTime =>
      torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ))) :=
    ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_snd)).pow_const _)
  obtain ⟨hi, he⟩ := ipsiWeighted_integral_comp_proj ht ht1 x
    (Θ := fun u v => torusParabolicSize (u - v) ^ (-(1 : ℝ))) hm
    (fun u v => Real.rpow_nonneg (torusParabolicSize_nonneg _) _) hI
  refine ⟨hi, ?_⟩
  rw [he]
  have := h.2
  simpa only [ipsiWeightedPeriodised_abs] using this

/-- **Second moment of `Q_t Π_x I(Ψ)Ψ (x)`, [Hai14, (10.2)] for the product `I(Ψ)Ψ`.** -/
theorem hairerIPsiPsiField_semigroup_second_moment_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, (∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) ^ 2 ∂P ≤
          C * (t ^ (1 / 4 : ℝ)) ^ (2 * (1 - 2 * κ) + κ) := by
  obtain ⟨Cc, hCc, hdom⟩ := ipsi_tested_cov_dominated.{u} N hρ (θ := κ / 2) (γ := 1 - κ / 2)
    (δ := κ) (by linarith) (by linarith) (by linarith) (by linarith) hκ (by linarith)
  obtain ⟨K1, hK1, hI1⟩ := ipsi_majorant_integral_le (θ := κ / 2) (by linarith) (by linarith)
  obtain ⟨K2, hK2, hI2⟩ := ipsi_majorant_integral_inv_le
  refine ⟨Cc * (K1 + K2), by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  set l := t ^ (1 / 4 : ℝ) with hl
  rw [hairerIPsiPsiField_integral_sq_eq.{u} N hρ hW hε hξ ht x]
  obtain ⟨i1, e1⟩ := hI1 ht ht1 x
  obtain ⟨i2, e2⟩ := hI2 ht ht1 x
  have hd := hdom hW hε hξ ht ht1 x
  set A : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(κ / 2))) *
        (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-(κ / 2)))) with hA
  set B : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ)) with hB
  have hMi : Integrable (fun q => Cc * ((l ^ (1 - κ / 2) * l ^ (1 - κ / 2)) * A q +
      (l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2)) * B q)) :=
    (((i1.const_mul _).add (i2.const_mul _)).const_mul Cc)
  have h1 : ‖∫ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
      parabolicSemigroup.kernel t x q.2 *
      ∫ ω, hairerIPsiPsiField N ξ x ω q.1 * hairerIPsiPsiField N ξ x ω q.2 ∂P‖ ≤
      ∫ q, Cc * ((l ^ (1 - κ / 2) * l ^ (1 - κ / 2)) * A q +
        (l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2)) * B q) := by
    refine norm_integral_le_of_norm_le hMi ?_
    filter_upwards [hd] with q hq
    rw [Real.norm_eq_abs]
    exact hq
  have h2 : ∫ q : ParabolicSpace × ParabolicSpace, Cc * ((l ^ (1 - κ / 2) * l ^ (1 - κ / 2)) * A q +
        (l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2)) * B q) =
      Cc * ((l ^ (1 - κ / 2) * l ^ (1 - κ / 2)) * (∫ q, A q) +
        (l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2)) * (∫ q, B q)) := by
    rw [integral_const_mul, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
      integral_const_mul]
  have hg1 : 0 ≤ l ^ (1 - κ / 2) * l ^ (1 - κ / 2) := by positivity
  have hg2 : 0 ≤ l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2) := by positivity
  have h3 : Cc * ((l ^ (1 - κ / 2) * l ^ (1 - κ / 2)) * (∫ q, A q) +
        (l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2)) * (∫ q, B q)) ≤
      Cc * ((l ^ (1 - κ / 2) * l ^ (1 - κ / 2)) * (K1 * l ^ (-(2 * (κ / 2)))) +
        (l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2)) * (K2 * l ^ (-(1 : ℝ)))) :=
    mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left e1 hg1)
      (mul_le_mul_of_nonneg_left e2 hg2)) hCc
  have r1 : l ^ (1 - κ / 2) * l ^ (1 - κ / 2) * l ^ (-(2 * (κ / 2))) = l ^ (2 - 2 * κ) := by
    rw [← Real.rpow_add hlam, ← Real.rpow_add hlam]; congr 1; ring
  have r2 : l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2) * l ^ (-(1 : ℝ)) = l ^ (2 - κ) := by
    rw [← Real.rpow_add hlam, ← Real.rpow_add hlam]; congr 1; ring
  have r3 : l ^ (2 - 2 * κ) ≤ l ^ (2 * (1 - 2 * κ) + κ) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have r4 : l ^ (2 - κ) ≤ l ^ (2 * (1 - 2 * κ) + κ) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have hq0 := Real.rpow_nonneg hlam.le (2 * (1 - 2 * κ) + κ)
  have key : Cc * ((l ^ (1 - κ / 2) * l ^ (1 - κ / 2)) * (K1 * l ^ (-(2 * (κ / 2)))) +
        (l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2)) * (K2 * l ^ (-(1 : ℝ)))) =
      Cc * (K1 * l ^ (2 - 2 * κ) + K2 * l ^ (2 - κ)) := by
    rw [← r1, ← r2]; ring
  have hfin : Cc * (K1 * l ^ (2 - 2 * κ) + K2 * l ^ (2 - κ)) ≤
      Cc * (K1 + K2) * l ^ (2 * (1 - 2 * κ) + κ) := by
    have := mul_le_mul_of_nonneg_left r3 hK1
    have := mul_le_mul_of_nonneg_left r4 hK2
    nlinarith [mul_nonneg hCc (mul_nonneg hK1 hq0), mul_nonneg hCc (mul_nonneg hK2 hq0)]
  calc _ ≤ ‖∫ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
      parabolicSemigroup.kernel t x q.2 *
      ∫ ω, hairerIPsiPsiField N ξ x ω q.1 * hairerIPsiPsiField N ξ x ω q.2 ∂P‖ :=
        Real.le_norm_self _
    _ ≤ _ := h1.trans (by rw [h2]; exact h3.trans (key ▸ hfin))

end RegularityStructures.Phi43

end
