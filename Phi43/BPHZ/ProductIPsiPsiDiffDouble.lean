/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondBound
import Mathlib.Tactic

/-!
# Double bounds with two different exponents

`ipsiWeighted_doubleBound_ab`: `∬ g(u) g(v) (1 + s(u - x)^(-a)) (1 + s(v - x)^(-b)) ≲ lam^(-(a+b))`,
and its transfer to the product `ParabolicSpace × ParabolicSpace` against the weighted semigroup
kernel (`ipsi_majorant_integral_ab_le`, `ipsi_majorant_integral_inv_le_of_exp`).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Two-exponent weighted double bound.** -/
theorem ipsiWeighted_doubleBound_ab {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ha5 : a < 5)
    (hb5 : b < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupDoubleBound (ipsiWeightedPeriodised t x)
        (fun u v => (1 + torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-a)) *
          (1 + torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-b)))
        (K * (t ^ (1 / 4 : ℝ)) ^ (-(a + b))) := by
  obtain ⟨B, hB0, hB⟩ := ipsiWeighted_profile
  refine ⟨|semigroupTestDoubleConst B ipsiMom 0 0| +
    |semigroupTestDoubleConst B ipsiMom (-a) 0| +
    |semigroupTestDoubleConst B ipsiMom (-b) 0| +
    |semigroupTestMomConst B ipsiMom (-a) * semigroupTestMomConst B ipsiMom (-b)|,
    by positivity, fun {t} ht ht1 x => ?_⟩
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  set l := t ^ (1 / 4 : ℝ) with hl
  have d0 := h.doubleBound_fst (ζ := 0) (e := 0) (by norm_num) (by norm_num) hlam
  have d1 := h.doubleBound_fst (ζ := -a) (e := 0) (by linarith) (by norm_num) hlam
  have d2 := h.doubleBound_snd (ζ := -b) (e := 0) (by linarith) (by norm_num) hlam
  have d3 := h.doubleBound_mul (a := -a) (b := -b) (by linarith) (by linarith) hlam
  have s := d0.add (d1.add (d2.add d3))
  have e : ∀ u v : SpaceTime,
      torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (0 : ℝ) +
      (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-a) * torusParabolicSize (u - v) ^ (0 : ℝ) +
        (torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-b) * torusParabolicSize (u - v) ^ (0 : ℝ) +
          torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-a) *
            torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-b))) =
      (1 + torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-a)) *
        (1 + torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-b)) := fun u v => by
    simp only [Real.rpow_zero]; ring
  have s' := s.congr_ae (G := fun u v =>
    (1 + torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-a)) *
        (1 + torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-b)))
    (Filter.Eventually.of_forall fun w => e w.1 w.2)
  refine s'.mono_right ?_
  have p1 : l ^ (0 + 0 : ℝ) ≤ l ^ (-(a + b)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have p2 : l ^ (-a + 0 : ℝ) ≤ l ^ (-(a + b)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have p2' : l ^ (-b + 0 : ℝ) ≤ l ^ (-(a + b)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have p3 : l ^ (-a + -b : ℝ) = l ^ (-(a + b)) := by congr 1; ring
  have hq := Real.rpow_nonneg hlam.le (-(a + b))
  have b0 : semigroupTestDoubleConst B ipsiMom 0 0 * l ^ (0 + 0 : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom 0 0| * l ^ (-(a + b)) :=
    mul_le_mul (le_abs_self _) p1 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b1 : semigroupTestDoubleConst B ipsiMom (-a) 0 * l ^ (-a + 0 : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom (-a) 0| * l ^ (-(a + b)) :=
    mul_le_mul (le_abs_self _) p2 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b2 : semigroupTestDoubleConst B ipsiMom (-b) 0 * l ^ (-b + 0 : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom (-b) 0| * l ^ (-(a + b)) :=
    mul_le_mul (le_abs_self _) p2' (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b3 : semigroupTestMomConst B ipsiMom (-a) * semigroupTestMomConst B ipsiMom (-b) *
      l ^ (-a + -b : ℝ) ≤
      |semigroupTestMomConst B ipsiMom (-a) * semigroupTestMomConst B ipsiMom (-b)| *
        l ^ (-(a + b)) := by
    rw [p3]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hq
  have := add_le_add b0 (add_le_add b1 (add_le_add b2 b3))
  calc _ ≤ _ := this
    _ = _ := by ring

end RegularityStructures

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The `ℝ⁴ × ℝ⁴` integral of the weighted kernel against the two-exponent weight. -/
theorem ipsi_majorant_integral_ab_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ha5 : a < 5)
    (hb5 : b < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      Integrable (fun q : ParabolicSpace × ParabolicSpace => ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-a)) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-b)))) ∧
      ∫ q : ParabolicSpace × ParabolicSpace, ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-a)) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-b))) ≤
        K * (t ^ (1 / 4 : ℝ)) ^ (-(a + b)) := by
  obtain ⟨K, hK, hD⟩ := ipsiWeighted_doubleBound_ab ha hb ha5 hb5
  refine ⟨K, hK, fun {t} ht ht1 x => ?_⟩
  have h := hD ht ht1 x
  have hI : Integrable (fun w : SpaceTime × SpaceTime => ipsiWeightedPeriodised t x w.1 *
      ipsiWeightedPeriodised t x w.2 * ((1 + torusParabolicSize (w.1 - spaceTimeProj x) ^ (-a)) *
        (1 + torusParabolicSize (w.2 - spaceTimeProj x) ^ (-b)))) := by
    have := h.1
    simpa only [ipsiWeightedPeriodised_abs] using this
  have hm : Measurable (fun w : SpaceTime × SpaceTime =>
      (1 + torusParabolicSize (w.1 - spaceTimeProj x) ^ (-a)) *
        (1 + torusParabolicSize (w.2 - spaceTimeProj x) ^ (-b))) := by
    have m1 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.1 - spaceTimeProj x) ^ (-a)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_const)).pow_const _)
    have m2 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.2 - spaceTimeProj x) ^ (-b)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_const)).pow_const _)
    exact (measurable_const.add m1).mul (measurable_const.add m2)
  have hnn : ∀ u v : SpaceTime, 0 ≤ (1 + torusParabolicSize (u - spaceTimeProj x) ^ (-a)) *
      (1 + torusParabolicSize (v - spaceTimeProj x) ^ (-b)) := fun u v => by
    have a1 := Real.rpow_nonneg (torusParabolicSize_nonneg (u - spaceTimeProj x)) (-a)
    have a2 := Real.rpow_nonneg (torusParabolicSize_nonneg (v - spaceTimeProj x)) (-b)
    positivity
  obtain ⟨hi, he⟩ := ipsiWeighted_integral_comp_proj ht ht1 x
    (Θ := fun u v => (1 + torusParabolicSize (u - spaceTimeProj x) ^ (-a)) *
      (1 + torusParabolicSize (v - spaceTimeProj x) ^ (-b))) hm hnn hI
  refine ⟨hi, ?_⟩
  rw [he]
  have := h.2
  simpa only [ipsiWeightedPeriodised_abs] using this

/-- The `ℝ⁴ × ℝ⁴` integral of the weighted kernel against `s(u - v)^(-e)`. -/
theorem ipsi_majorant_integral_inv_le_of_exp {e : ℝ} (he5 : e < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      Integrable (fun q : ParabolicSpace × ParabolicSpace => ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-e)) ∧
      ∫ q : ParabolicSpace × ParabolicSpace, ipsiWeightedKernel t x q.1 *
        ipsiWeightedKernel t x q.2 *
        torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-e) ≤
        K * (t ^ (1 / 4 : ℝ)) ^ (-e) := by
  obtain ⟨K, hK, hD⟩ := ipsiWeighted_doubleBound_inv he5
  refine ⟨K, hK, fun {t} ht ht1 x => ?_⟩
  have h := hD ht ht1 x
  have hI : Integrable (fun w : SpaceTime × SpaceTime => ipsiWeightedPeriodised t x w.1 *
      ipsiWeightedPeriodised t x w.2 * torusParabolicSize (w.1 - w.2) ^ (-e)) := by
    have := h.1
    simpa only [ipsiWeightedPeriodised_abs] using this
  have hm : Measurable (fun w : SpaceTime × SpaceTime =>
      torusParabolicSize (w.1 - w.2) ^ (-e)) :=
    ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_snd)).pow_const _)
  obtain ⟨hi, he⟩ := ipsiWeighted_integral_comp_proj ht ht1 x
    (Θ := fun u v => torusParabolicSize (u - v) ^ (-e)) hm
    (fun u v => Real.rpow_nonneg (torusParabolicSize_nonneg _) _) hI
  refine ⟨hi, ?_⟩
  rw [he]
  have := h.2
  simpa only [ipsiWeightedPeriodised_abs] using this

end RegularityStructures.Phi43

end
