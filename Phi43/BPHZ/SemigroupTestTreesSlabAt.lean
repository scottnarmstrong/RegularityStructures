/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesSlab

/-!
# Singular powers on a time slab centred at a general time

The slab `{w : |w.1 - τ| ≤ T}` has volume `2 T`.  A centred power `s(c - w)^(-a)`, `0 < a < 5`,
restricted to the slab has integral at most `80/(5 - a) + 2 T` whatever the centre `c`
(`singularIntLe_slabAt_singularPow`); products of two and of three powers of total order `< 5` are
dominated pointwise by sums of single powers (`singularPow_mul_le`), whence the bound
`singularIntLe_slabAt_mul_two` for two powers.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem measurableSet_abs_fst_sub_le (τ T : ℝ) : MeasurableSet {w : SpaceTime | |w.1 - τ| ≤ T} :=
  measurableSet_le (continuous_abs.measurable.comp (measurable_fst.sub measurable_const))
    measurable_const

theorem volume_abs_fst_sub_le (τ T : ℝ) :
    volume {w : SpaceTime | |w.1 - τ| ≤ T} = ENNReal.ofReal (2 * T) := by
  have : {w : SpaceTime | |w.1 - τ| ≤ T} = Set.Icc (τ - T) (τ + T) ×ˢ (Set.univ : Set Torus3) := by
    ext w
    simp only [Set.mem_ofPred_eq, abs_le, Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, volume_univ_torus3,
    mul_one]
  congr 1
  ring

/-- A centred power on a time slab, uniformly in the centre. -/
theorem singularIntLe_slabAt_singularPow {a T : ℝ} (τ : ℝ) (ha : 0 < a) (ha5 : a < 5)
    (hT : 0 ≤ T) (c : SpaceTime) :
    SingularIntLe (Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T} (singularPow a c))
      (80 / (5 - a) + 2 * T) := by
  have iL := integrable_singularLocalWeight ha ha5 (by norm_num : (0 : ℝ) < 1)
  have iLc := integrable_comp_sub_left_spaceTime iL c
  have hfin : volume {w : SpaceTime | |w.1 - τ| ≤ T} < ⊤ := by
    rw [volume_abs_fst_sub_le]
    exact ENNReal.ofReal_lt_top
  have iI : Integrable (Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T} (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hfin.ne).integrable_indicator
      (measurableSet_abs_fst_sub_le τ T)
  have hI : ∫ w, Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T} (fun _ => (1 : ℝ)) w = 2 * T := by
    rw [integral_indicator_const _ (measurableSet_abs_fst_sub_le τ T), measureReal_def,
      volume_abs_fst_sub_le, ENNReal.toReal_ofReal (by linarith)]
    simp
  have hf : SingularIntLe (fun w => singularLocalWeight a 1 (c - w) +
      Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T} (fun _ => (1 : ℝ)) w)
      (80 / (5 - a) + 2 * T) := by
    refine ⟨iLc.add iI, ?_⟩
    rw [integral_add iLc iI, integral_comp_sub_left_spaceTime (singularLocalWeight a 1) c, hI]
    have := integral_singularLocalWeight_le ha ha5 (by norm_num : (0 : ℝ) < 1)
    simpa using add_le_add_right this (2 * T)
  refine hf.of_le ?_ ?_ ?_
  · exact ((measurable_singularPow a c).indicator
      (measurableSet_abs_fst_sub_le τ T)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w => Set.indicator_nonneg
      (fun w _ => singularPow_nonneg _ _ _) w
  · refine Filter.Eventually.of_forall fun w => ?_
    by_cases hw : w ∈ {w : SpaceTime | |w.1 - τ| ≤ T}
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      have := SemigroupTestProfile.rpow_neg_le_localWeight_add ha (by norm_num : (0 : ℝ) < 1)
        (c - w)
      simpa [singularPow] using this
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      simpa using singularLocalWeight_nonneg a 1 (c - w)

/-- Two centred powers of total order `< 5` on a time slab, uniformly in the centres. -/
theorem singularIntLe_slabAt_mul_two {a b T : ℝ} (τ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < 5) (hT : 0 ≤ T) (p q : SpaceTime) :
    SingularIntLe (Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T}
      (fun w => singularPow a p w * singularPow b q w))
      (2 * (80 / (5 - (a + b)) + 2 * T)) := by
  have hs := (singularIntLe_slabAt_singularPow τ (a := a + b) (T := T) (by linarith) hab hT p).add
    (singularIntLe_slabAt_singularPow τ (a := a + b) (T := T) (by linarith) hab hT q)
  refine (hs.mono_right (le_of_eq (by ring))).of_le ?_ ?_ ?_
  · exact (((measurable_singularPow a p).mul (measurable_singularPow b q)).indicator
      (measurableSet_abs_fst_sub_le τ T)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w => Set.indicator_nonneg
      (fun w _ => mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) w
  · filter_upwards [ae_torusParabolicSize_sub_pos p, ae_torusParabolicSize_sub_pos q] with w hp hq
    by_cases hw : w ∈ {w : SpaceTime | |w.1 - τ| ≤ T}
    · simp only [Set.indicator_of_mem hw]
      exact singularPow_mul_le ha.le hb.le hp hq
    · simp only [Set.indicator_of_notMem hw]
      simp

end RegularityStructures

end
