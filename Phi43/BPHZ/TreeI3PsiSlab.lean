/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiLeaves

/-!
# Two centred powers of total order `< 5` on a time slab

On the slab `|t| ≤ 2` the product of two centred parabolic powers of total order `a + b < 5`,
with centres of parabolic size at most `1`, is integrable with an integral bounded uniformly in
the centres.  This is the bounded case of [Hai14, Lemma 10.14] with an explicit time cut-off.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14, (10.37a).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- On the slab `|t| ≤ 2` the parabolic size is at most `3`. -/
theorem torusParabolicSize_le_three_of_abs_le_two {w : SpaceTime} (hw : |w.1| ≤ 2) :
    torusParabolicSize w ≤ 3 := by
  have h1 : √|w.1| ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have h2 := torusSpatialNorm_le_seven_eighth w.2
  unfold torusParabolicSize
  linarith

theorem measurableSet_slab : MeasurableSet {w : SpaceTime | |w.1| ≤ 2} :=
  measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const

/-- Two centred powers of total order `< 5` on the slab `|t| ≤ 2`. -/
theorem singularIntLe_slab_mul_two {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : SpaceTime, torusParabolicSize p ≤ 1 → torusParabolicSize q ≤ 1 →
      SingularIntLe (Set.indicator {w : SpaceTime | |w.1| ≤ 2}
        (fun w => singularPow a p w * singularPow b q w)) C := by
  have hp : 0 < a + b := by linarith
  have h5 : 0 < 5 - (a + b) := by linarith
  refine ⟨2 * (80 / (5 - (a + b)) * (32 : ℝ) ^ (5 - (a + b))),
    mul_nonneg (by norm_num) (mul_nonneg (div_nonneg (by norm_num) h5.le)
      (Real.rpow_nonneg (by norm_num) _)), fun p q hp1 hq1 => ?_⟩
  have iL := integrable_singularLocalWeight hp hab (by norm_num : (0 : ℝ) < 32)
  have iLp := integrable_comp_sub_left_spaceTime iL p
  have iLq := integrable_comp_sub_left_spaceTime iL q
  have hb32 := integral_singularLocalWeight_le hp hab (by norm_num : (0 : ℝ) < 32)
  have hf : SingularIntLe (fun w => singularLocalWeight (a + b) 32 (p - w) +
      singularLocalWeight (a + b) 32 (q - w))
      (2 * (80 / (5 - (a + b)) * (32 : ℝ) ^ (5 - (a + b)))) := by
    refine ⟨iLp.add iLq, ?_⟩
    rw [integral_add iLp iLq, integral_comp_sub_left_spaceTime (singularLocalWeight (a + b) 32) p,
      integral_comp_sub_left_spaceTime (singularLocalWeight (a + b) 32) q]
    linarith
  refine hf.of_le ?_ ?_ ?_
  · exact (((measurable_singularPow a p).mul (measurable_singularPow b q)).indicator
      measurableSet_slab).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w => Set.indicator_nonneg
      (fun w _ => mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) w
  · filter_upwards [ae_torusParabolicSize_sub_pos p, ae_torusParabolicSize_sub_pos q]
      with w hpw hqw
    by_cases hw : |w.1| ≤ 2
    · rw [Set.indicator_of_mem (show w ∈ {w : SpaceTime | |w.1| ≤ 2} from hw)]
      have h3 := torusParabolicSize_le_three_of_abs_le_two hw
      have e1 := torusParabolicSize_sub_le_eight_mul p w
      have e2 := torusParabolicSize_sub_le_eight_mul q w
      have hLp : singularLocalWeight (a + b) 32 (p - w) = singularPow (a + b) p w := by
        have h32 : torusParabolicSize (p - w) ≤ 32 := by linarith
        simp [singularLocalWeight, singularPow, hpw, h32]
      have hLq : singularLocalWeight (a + b) 32 (q - w) = singularPow (a + b) q w := by
        have h32 : torusParabolicSize (q - w) ≤ 32 := by linarith
        simp [singularLocalWeight, singularPow, hqw, h32]
      rw [hLp, hLq]
      exact singularPow_mul_le ha.le hb.le hpw hqw
    · rw [Set.indicator_of_notMem (show w ∉ {w : SpaceTime | |w.1| ≤ 2} from hw)]
      exact add_nonneg (singularLocalWeight_nonneg _ _ _) (singularLocalWeight_nonneg _ _ _)

end RegularityStructures

end
