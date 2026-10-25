/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffDouble
import Mathlib.Tactic

/-!
# Two-exponent weighted double bound with a singular factor

`ipsiWeighted_doubleBound_ab_inv`:
`∬ g(u) g(v) (1 + s(u - x)^(-a)) (1 + s(v - x)^(-b)) s(u - v)^(-ν) ≲ lam^(-(a + b + ν))`,
through the weighted Young inequality `u^(-a) v^(-b) ≤ a/(a+b) u^(-(a+b)) + b/(a+b) v^(-(a+b))`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem ipsi_young_rpow {u v a b : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 < a) (hb : 0 < b) :
    u ^ (-a) * v ^ (-b) ≤ (a / (a + b)) * u ^ (-(a + b)) + (b / (a + b)) * v ^ (-(a + b)) := by
  have hab : 0 < a + b := by linarith
  have n1 : 0 ≤ u ^ (-(a + b)) := Real.rpow_nonneg hu _
  have n2 : 0 ≤ v ^ (-(a + b)) := Real.rpow_nonneg hv _
  rcases hu.eq_or_lt with h0 | hu'
  · subst h0
    rw [Real.zero_rpow (by linarith : (-a : ℝ) ≠ 0), zero_mul]
    positivity
  rcases hv.eq_or_lt with h0 | hv'
  · subst h0
    rw [Real.zero_rpow (by linarith : (-b : ℝ) ≠ 0), mul_zero]
    positivity
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := a / (a + b)) (w₂ := b / (a + b))
    (p₁ := u ^ (-(a + b))) (p₂ := v ^ (-(a + b))) (by positivity) (by positivity) n1 n2
    (by field_simp)
  have e1 : (u ^ (-(a + b))) ^ (a / (a + b)) = u ^ (-a) := by
    rw [← Real.rpow_mul hu]; congr 1; field_simp
  have e2 : (v ^ (-(a + b))) ^ (b / (a + b)) = v ^ (-b) := by
    rw [← Real.rpow_mul hv]; congr 1; field_simp
  rw [e1, e2] at h
  exact h

/-- **Two-exponent weighted double bound with the factor `s(u - v)^(-ν)`.** -/
theorem ipsiWeighted_doubleBound_ab_inv {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < 5) (hν5 : ν < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupDoubleBound (ipsiWeightedPeriodised t x)
        (fun u v => (1 + torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-a)) *
          (1 + torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-b)) *
          torusParabolicSize (u - v) ^ (-ν))
        (K * (t ^ (1 / 4 : ℝ)) ^ (-(a + b + ν))) := by
  obtain ⟨B, hB0, hB⟩ := ipsiWeighted_profile
  refine ⟨|semigroupTestDoubleConst B ipsiMom 0 (-ν)| +
    |semigroupTestDoubleConst B ipsiMom (-a) (-ν)| +
    |semigroupTestDoubleConst B ipsiMom (-b) (-ν)| +
    |semigroupTestDoubleConst B ipsiMom (-(a + b)) (-ν)|, by positivity, fun {t} ht ht1 x => ?_⟩
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  set l := t ^ (1 / 4 : ℝ) with hl
  set px := Phi43.spaceTimeProj x with hpx
  have hw1 : 0 < a / (a + b) := by positivity
  have hw2 : 0 < b / (a + b) := by positivity
  have hw : a / (a + b) + b / (a + b) = 1 := by field_simp
  have d0 := h.doubleBound_fst (ζ := 0) (e := -ν) (by norm_num) (by linarith) hlam
  have d1 := h.doubleBound_fst (ζ := -a) (e := -ν) (by linarith) (by linarith) hlam
  have d2 := h.doubleBound_snd (ζ := -b) (e := -ν) (by linarith) (by linarith) hlam
  have d4 := h.doubleBound_fst (ζ := -(a + b)) (e := -ν) (by linarith) (by linarith) hlam
  have d5 := h.doubleBound_snd (ζ := -(a + b)) (e := -ν) (by linarith) (by linarith) hlam
  have sG := d0.add (d1.add (d2.add ((d4.const_mul (c := a / (a + b)) hw1.le).add
    (d5.const_mul (c := b / (a + b)) hw2.le))))
  have hmeas : AEStronglyMeasurable (fun w : SpaceTime × SpaceTime =>
      (1 + torusParabolicSize (w.1 - px) ^ (-a)) * (1 + torusParabolicSize (w.2 - px) ^ (-b)) *
        torusParabolicSize (w.1 - w.2) ^ (-ν)) volume := by
    have m1 : Measurable (fun w : SpaceTime × SpaceTime => torusParabolicSize (w.1 - px) ^ (-a)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_const)).pow_const _)
    have m2 : Measurable (fun w : SpaceTime × SpaceTime => torusParabolicSize (w.2 - px) ^ (-b)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_const)).pow_const _)
    have m3 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.1 - w.2) ^ (-ν)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_snd)).pow_const _)
    exact (((measurable_const.add m1).mul (measurable_const.add m2)).mul m3).aestronglyMeasurable
  have hAbs := SemigroupDoubleBound.of_abs_le (g := ipsiWeightedPeriodised t x)
    (F := fun u v => (1 + torusParabolicSize (u - px) ^ (-a)) *
      (1 + torusParabolicSize (v - px) ^ (-b)) * torusParabolicSize (u - v) ^ (-ν))
    (G := fun u v =>
      torusParabolicSize (u - px) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (-ν) +
      (torusParabolicSize (u - px) ^ (-a) * torusParabolicSize (u - v) ^ (-ν) +
        (torusParabolicSize (v - px) ^ (-b) * torusParabolicSize (u - v) ^ (-ν) +
          (a / (a + b) * (torusParabolicSize (u - px) ^ (-(a + b)) *
              torusParabolicSize (u - v) ^ (-ν)) +
            b / (a + b) * (torusParabolicSize (v - px) ^ (-(a + b)) *
              torusParabolicSize (u - v) ^ (-ν))))))
    (measurable_ipsiWeightedPeriodised t x) sG hmeas
    (Filter.Eventually.of_forall fun w => by
      have n1 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - px)) (-a)
      have n2 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.2 - px)) (-b)
      have n3 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - w.2)) (-ν)
      rw [Real.rpow_zero, abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) n3)]
      have young := ipsi_young_rpow (torusParabolicSize_nonneg (w.1 - px))
        (torusParabolicSize_nonneg (w.2 - px)) ha hb
      have k := mul_le_mul_of_nonneg_left young n3
      nlinarith only [k])
  have hAbs' := hAbs.congr_ae (G := fun u v =>
    (1 + torusParabolicSize (u - px) ^ (-a)) * (1 + torusParabolicSize (v - px) ^ (-b)) *
      torusParabolicSize (u - v) ^ (-ν))
    (Filter.Eventually.of_forall fun w => by
      have n1 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - px)) (-a)
      have n2 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.2 - px)) (-b)
      have n3 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - w.2)) (-ν)
      exact abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) n3))
  refine hAbs'.mono_right ?_
  have q0 : l ^ (0 + -ν : ℝ) ≤ l ^ (-(a + b + ν)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have q1 : l ^ (-a + -ν : ℝ) ≤ l ^ (-(a + b + ν)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have q2 : l ^ (-b + -ν : ℝ) ≤ l ^ (-(a + b + ν)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have q4 : l ^ (-(a + b) + -ν : ℝ) = l ^ (-(a + b + ν)) := by congr 1; ring
  have hq := Real.rpow_nonneg hlam.le (-(a + b + ν))
  have b0 : semigroupTestDoubleConst B ipsiMom 0 (-ν) * l ^ (0 + -ν : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom 0 (-ν)| * l ^ (-(a + b + ν)) :=
    mul_le_mul (le_abs_self _) q0 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b1 : semigroupTestDoubleConst B ipsiMom (-a) (-ν) * l ^ (-a + -ν : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom (-a) (-ν)| * l ^ (-(a + b + ν)) :=
    mul_le_mul (le_abs_self _) q1 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b2 : semigroupTestDoubleConst B ipsiMom (-b) (-ν) * l ^ (-b + -ν : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom (-b) (-ν)| * l ^ (-(a + b + ν)) :=
    mul_le_mul (le_abs_self _) q2 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b4 : a / (a + b) * (semigroupTestDoubleConst B ipsiMom (-(a + b)) (-ν) *
        l ^ (-(a + b) + -ν : ℝ)) + b / (a + b) * (semigroupTestDoubleConst B ipsiMom (-(a + b)) (-ν) *
        l ^ (-(a + b) + -ν : ℝ)) ≤
      |semigroupTestDoubleConst B ipsiMom (-(a + b)) (-ν)| * l ^ (-(a + b + ν)) := by
    rw [← add_mul, hw, one_mul, q4]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hq
  have := add_le_add b0 (add_le_add b1 (add_le_add b2 b4))
  calc _ ≤ _ := this
    _ = _ := by ring

end RegularityStructures

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The `ℝ⁴ × ℝ⁴` integral of the weighted kernel against `Θ_{a,b}(u,v) s(u - v)^(-ν)`. -/
theorem ipsi_majorant_integral_ab_inv_le {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < 5)
    (hν5 : ν < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      Integrable (fun q : ParabolicSpace × ParabolicSpace => ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-a)) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-b))) *
          torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-ν))) ∧
      ∫ q : ParabolicSpace × ParabolicSpace, ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-a)) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-b))) *
          torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-ν)) ≤
        K * (t ^ (1 / 4 : ℝ)) ^ (-(a + b + ν)) := by
  obtain ⟨K, hK, hD⟩ := ipsiWeighted_doubleBound_ab_inv ha hb hab hν5
  refine ⟨K, hK, fun {t} ht ht1 x => ?_⟩
  have h := hD ht ht1 x
  have hI : Integrable (fun w : SpaceTime × SpaceTime => ipsiWeightedPeriodised t x w.1 *
      ipsiWeightedPeriodised t x w.2 *
      (((1 + torusParabolicSize (w.1 - spaceTimeProj x) ^ (-a)) *
        (1 + torusParabolicSize (w.2 - spaceTimeProj x) ^ (-b))) *
        torusParabolicSize (w.1 - w.2) ^ (-ν))) := by
    have := h.1
    simpa only [ipsiWeightedPeriodised_abs, mul_assoc] using this
  have hm : Measurable (fun w : SpaceTime × SpaceTime =>
      ((1 + torusParabolicSize (w.1 - spaceTimeProj x) ^ (-a)) *
        (1 + torusParabolicSize (w.2 - spaceTimeProj x) ^ (-b))) *
        torusParabolicSize (w.1 - w.2) ^ (-ν)) := by
    have m1 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.1 - spaceTimeProj x) ^ (-a)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_const)).pow_const _)
    have m2 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.2 - spaceTimeProj x) ^ (-b)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_const)).pow_const _)
    have m3 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.1 - w.2) ^ (-ν)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_snd)).pow_const _)
    exact ((measurable_const.add m1).mul (measurable_const.add m2)).mul m3
  have hnn : ∀ u v : SpaceTime, 0 ≤ ((1 + torusParabolicSize (u - spaceTimeProj x) ^ (-a)) *
      (1 + torusParabolicSize (v - spaceTimeProj x) ^ (-b))) *
        torusParabolicSize (u - v) ^ (-ν) := fun u v => by
    have a1 := Real.rpow_nonneg (torusParabolicSize_nonneg (u - spaceTimeProj x)) (-a)
    have a2 := Real.rpow_nonneg (torusParabolicSize_nonneg (v - spaceTimeProj x)) (-b)
    have a3 := Real.rpow_nonneg (torusParabolicSize_nonneg (u - v)) (-ν)
    positivity
  obtain ⟨hi, he⟩ := ipsiWeighted_integral_comp_proj ht ht1 x
    (Θ := fun u v => ((1 + torusParabolicSize (u - spaceTimeProj x) ^ (-a)) *
      (1 + torusParabolicSize (v - spaceTimeProj x) ^ (-b))) *
        torusParabolicSize (u - v) ^ (-ν)) hm hnn hI
  refine ⟨hi, ?_⟩
  rw [he]
  have := h.2
  simpa only [ipsiWeightedPeriodised_abs, mul_assoc] using this

end RegularityStructures.Phi43

end
