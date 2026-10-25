/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondTransfer
public import Phi43.BPHZ.SemigroupTestTreesBound
import Mathlib.Tactic

/-!
# Double bounds for the weighted profile

For the profile `g = ipsiWeightedPeriodised t x` at scale `lam = t^(1/4)`:

* `ipsiWeighted_doubleBound_theta`:
  `∬ g(u) g(v) (1 + s(u - x)^(-θ)) (1 + s(v - x)^(-θ)) ≲ lam^(-2θ)`;
* `ipsiWeighted_doubleBound_inv`: `∬ g(u) g(v) s(u - v)^(-e) ≲ lam^(-e)`, `0 < e < 5`;
* `ipsiWeighted_doubleBound_theta_inv`:
  `∬ g(u) g(v) (1 + s(u - x)^(-θ)) (1 + s(v - x)^(-θ)) s(u - v)^(-1) ≲ lam^(-1-2θ)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem ipsiWeightedPeriodised_abs (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) :
    |ipsiWeightedPeriodised t x u| = ipsiWeightedPeriodised t x u :=
  abs_of_nonneg (ipsiWeightedPeriodised_nonneg t x u)

theorem ipsiWeighted_profile :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupTestProfile (Phi43.spaceTimeProj x) (t ^ (1 / 4 : ℝ)) B ipsiMom
        (ipsiWeightedPeriodised t x) := by
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_ipsiWeighted
  exact ⟨B, hB0, fun {t} ht ht1 x => hB ht ht1 x⟩

/-- **`θ`-weighted double bound.** -/
theorem ipsiWeighted_doubleBound_theta {θ : ℝ} (hθ : 0 < θ) (hθ5 : θ < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupDoubleBound (ipsiWeightedPeriodised t x)
        (fun u v => (1 + torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-θ)) *
          (1 + torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-θ)))
        (K * (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ))) := by
  obtain ⟨B, hB0, hB⟩ := ipsiWeighted_profile
  refine ⟨|semigroupTestDoubleConst B ipsiMom 0 0| +
    2 * |semigroupTestDoubleConst B ipsiMom (-θ) 0| +
    |semigroupTestMomConst B ipsiMom (-θ) * semigroupTestMomConst B ipsiMom (-θ)|,
    by positivity, fun {t} ht ht1 x => ?_⟩
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  set l := t ^ (1 / 4 : ℝ) with hl
  have d0 := h.doubleBound_fst (ζ := 0) (e := 0) (by norm_num) (by norm_num) hlam
  have d1 := h.doubleBound_fst (ζ := -θ) (e := 0) (by linarith) (by norm_num) hlam
  have d2 := h.doubleBound_snd (ζ := -θ) (e := 0) (by linarith) (by norm_num) hlam
  have d3 := h.doubleBound_mul (a := -θ) (b := -θ) (by linarith) (by linarith) hlam
  have s := d0.add (d1.add (d2.add d3))
  have e : ∀ u v : SpaceTime,
      torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (0 : ℝ) +
      (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-θ) * torusParabolicSize (u - v) ^ (0 : ℝ) +
        (torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-θ) * torusParabolicSize (u - v) ^ (0 : ℝ) +
          torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-θ) *
            torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-θ))) =
      (1 + torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-θ)) *
        (1 + torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-θ)) := fun u v => by
    simp only [Real.rpow_zero]; ring
  have s' := s.congr_ae (G := fun u v =>
    (1 + torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-θ)) *
        (1 + torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-θ)))
    (Filter.Eventually.of_forall fun w => e w.1 w.2)
  refine s'.mono_right ?_
  have p1 : l ^ (0 + 0 : ℝ) ≤ l ^ (-(2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have p2 : l ^ (-θ + 0 : ℝ) ≤ l ^ (-(2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have p3 : l ^ (-θ + -θ : ℝ) = l ^ (-(2 * θ)) := by congr 1; ring
  have hq := Real.rpow_nonneg hlam.le (-(2 * θ))
  have hd0 := h.semigroupTestDoubleConst_nonneg hlam (ζ := 0) (e := 0) (by norm_num) (by norm_num)
    (by norm_num)
  have hd1 := h.semigroupTestDoubleConst_nonneg hlam (ζ := -θ) (e := 0) (by linarith)
    (by norm_num) (by linarith)
  have hm1 := h.semigroupTestMomConst_nonneg hlam (a := -θ) (by linarith)
  have b0 : semigroupTestDoubleConst B ipsiMom 0 0 * l ^ (0 + 0 : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom 0 0| * l ^ (-(2 * θ)) :=
    mul_le_mul (le_abs_self _) p1 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b1 : semigroupTestDoubleConst B ipsiMom (-θ) 0 * l ^ (-θ + 0 : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom (-θ) 0| * l ^ (-(2 * θ)) :=
    mul_le_mul (le_abs_self _) p2 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b3 : semigroupTestMomConst B ipsiMom (-θ) * semigroupTestMomConst B ipsiMom (-θ) *
      l ^ (-θ + -θ : ℝ) ≤
      |semigroupTestMomConst B ipsiMom (-θ) * semigroupTestMomConst B ipsiMom (-θ)| *
        l ^ (-(2 * θ)) := by
    rw [p3]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hq
  have := add_le_add b0 (add_le_add b1 (add_le_add b1 b3))
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Negative power of `s(u - v)`.** -/
theorem ipsiWeighted_doubleBound_inv {e : ℝ} (he5 : e < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupDoubleBound (ipsiWeightedPeriodised t x)
        (fun u v => torusParabolicSize (u - v) ^ (-e)) (K * (t ^ (1 / 4 : ℝ)) ^ (-e)) := by
  obtain ⟨B, hB0, hB⟩ := ipsiWeighted_profile
  refine ⟨|semigroupTestDoubleConst B ipsiMom 0 (-e)|, abs_nonneg _, fun {t} ht ht1 x => ?_⟩
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have d := h.doubleBound_fst (ζ := 0) (e := -e) (by norm_num) (by linarith) hlam
  have d' := d.congr_ae (G := fun u v => torusParabolicSize (u - v) ^ (-e))
    (Filter.Eventually.of_forall fun w => by simp only [Real.rpow_zero, one_mul])
  refine d'.mono_right ?_
  have : (t ^ (1 / 4 : ℝ)) ^ ((0 : ℝ) + -e) = (t ^ (1 / 4 : ℝ)) ^ (-e) := by rw [zero_add]
  rw [this]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hlam.le _)

/-- **`θ`-weighted double bound with the singular factor `s(u - v)^(-1)`.** -/
theorem ipsiWeighted_doubleBound_theta_inv {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupDoubleBound (ipsiWeightedPeriodised t x)
        (fun u v => (1 + torusParabolicSize (u - Phi43.spaceTimeProj x) ^ (-θ)) *
          (1 + torusParabolicSize (v - Phi43.spaceTimeProj x) ^ (-θ)) *
          torusParabolicSize (u - v) ^ (-(1 : ℝ)))
        (K * (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * θ))) := by
  obtain ⟨B, hB0, hB⟩ := ipsiWeighted_profile
  refine ⟨|semigroupTestDoubleConst B ipsiMom 0 (-1)| +
    2 * |semigroupTestDoubleConst B ipsiMom (-θ) (-1)| +
    |semigroupTestDoubleConst B ipsiMom (-(2 * θ)) (-1)|, by positivity, fun {t} ht ht1 x => ?_⟩
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  set l := t ^ (1 / 4 : ℝ) with hl
  set px := Phi43.spaceTimeProj x with hpx
  have d0 := h.doubleBound_fst (ζ := 0) (e := -1) (by norm_num) (by norm_num) hlam
  have d1 := h.doubleBound_fst (ζ := -θ) (e := -1) (by linarith) (by norm_num) hlam
  have d2 := h.doubleBound_snd (ζ := -θ) (e := -1) (by linarith) (by norm_num) hlam
  have d4 := h.doubleBound_fst (ζ := -(2 * θ)) (e := -1) (by linarith) (by norm_num) hlam
  have d5 := h.doubleBound_snd (ζ := -(2 * θ)) (e := -1) (by linarith) (by norm_num) hlam
  have sG := d0.add (d1.add (d2.add ((d4.add d5).const_mul (c := 1 / 2) (by norm_num))))
  have hmeas : AEStronglyMeasurable (fun w : SpaceTime × SpaceTime =>
      (1 + torusParabolicSize (w.1 - px) ^ (-θ)) * (1 + torusParabolicSize (w.2 - px) ^ (-θ)) *
        torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ))) volume := by
    have m1 : Measurable (fun w : SpaceTime × SpaceTime => torusParabolicSize (w.1 - px) ^ (-θ)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_const)).pow_const _)
    have m2 : Measurable (fun w : SpaceTime × SpaceTime => torusParabolicSize (w.2 - px) ^ (-θ)) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_const)).pow_const _)
    have m3 : Measurable (fun w : SpaceTime × SpaceTime =>
        torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ))) :=
      ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_snd)).pow_const _)
    exact (((measurable_const.add m1).mul (measurable_const.add m2)).mul m3).aestronglyMeasurable
  have hAbs := SemigroupDoubleBound.of_abs_le (g := ipsiWeightedPeriodised t x)
    (F := fun u v => (1 + torusParabolicSize (u - px) ^ (-θ)) *
      (1 + torusParabolicSize (v - px) ^ (-θ)) * torusParabolicSize (u - v) ^ (-(1 : ℝ)))
    (G := fun u v =>
      torusParabolicSize (u - px) ^ (0 : ℝ) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
      (torusParabolicSize (u - px) ^ (-θ) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
        (torusParabolicSize (v - px) ^ (-θ) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
          (1 / 2) * (torusParabolicSize (u - px) ^ (-(2 * θ)) * torusParabolicSize (u - v) ^ (-1 : ℝ) +
            torusParabolicSize (v - px) ^ (-(2 * θ)) * torusParabolicSize (u - v) ^ (-1 : ℝ)))))
    (measurable_ipsiWeightedPeriodised t x) sG hmeas
    (Filter.Eventually.of_forall fun w => by
      have n1 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - px)) (-θ)
      have n2 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.2 - px)) (-θ)
      have n3 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - w.2)) (-(1 : ℝ))
      have q1 : torusParabolicSize (w.1 - px) ^ (-(2 * θ)) =
          (torusParabolicSize (w.1 - px) ^ (-θ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (torusParabolicSize_nonneg _)]
        congr 1; push_cast; ring
      have q2 : torusParabolicSize (w.2 - px) ^ (-(2 * θ)) =
          (torusParabolicSize (w.2 - px) ^ (-θ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (torusParabolicSize_nonneg _)]
        congr 1; push_cast; ring
      rw [q1, q2, Real.rpow_zero, abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) n3)]
      nlinarith [mul_nonneg (sq_nonneg (torusParabolicSize (w.1 - px) ^ (-θ) -
        torusParabolicSize (w.2 - px) ^ (-θ))) n3])
  have hAbs' := hAbs.congr_ae (G := fun u v =>
    (1 + torusParabolicSize (u - px) ^ (-θ)) * (1 + torusParabolicSize (v - px) ^ (-θ)) *
      torusParabolicSize (u - v) ^ (-(1 : ℝ)))
    (Filter.Eventually.of_forall fun w => by
      have n1 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - px)) (-θ)
      have n2 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.2 - px)) (-θ)
      have n3 := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - w.2)) (-(1 : ℝ))
      exact abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) n3))
  refine hAbs'.mono_right ?_
  have q0 : l ^ (0 + -1 : ℝ) ≤ l ^ (-(1 + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have q1 : l ^ (-θ + -1 : ℝ) ≤ l ^ (-(1 + 2 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have q4 : l ^ (-(2 * θ) + -1 : ℝ) = l ^ (-(1 + 2 * θ)) := by congr 1; ring
  have hq := Real.rpow_nonneg hlam.le (-(1 + 2 * θ))
  have b0 : semigroupTestDoubleConst B ipsiMom 0 (-1) * l ^ (0 + -1 : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom 0 (-1)| * l ^ (-(1 + 2 * θ)) :=
    mul_le_mul (le_abs_self _) q0 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b1 : semigroupTestDoubleConst B ipsiMom (-θ) (-1) * l ^ (-θ + -1 : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom (-θ) (-1)| * l ^ (-(1 + 2 * θ)) :=
    mul_le_mul (le_abs_self _) q1 (Real.rpow_nonneg hlam.le _) (abs_nonneg _)
  have b4 : semigroupTestDoubleConst B ipsiMom (-(2 * θ)) (-1) * l ^ (-(2 * θ) + -1 : ℝ) ≤
      |semigroupTestDoubleConst B ipsiMom (-(2 * θ)) (-1)| * l ^ (-(1 + 2 * θ)) := by
    rw [q4]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hq
  have := add_le_add b0 (add_le_add b1 (add_le_add b1 (mul_le_mul_of_nonneg_left
    (add_le_add b4 b4) (by norm_num : (0 : ℝ) ≤ 1 / 2))))
  calc _ ≤ _ := this
    _ = _ := by ring

end RegularityStructures

end
