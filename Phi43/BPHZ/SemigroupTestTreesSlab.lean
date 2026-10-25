/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiSlab
public import Phi43.BPHZ.SemigroupTestProfile
public import Phi43.BPHZ.TreeI3Psi2TestedSize

/-!
# Singular powers on a time slab, uniformly in the centre

For the recentred kernels `K(z - ·) - K(-·)` with compact time support, the integration variable
ranges over a slab `{|w.1| ≤ T}` with `T = |z.1| + 1`.  On such a slab a centred power
`s(c - w)^(-a)`, `0 < a < 5`, has integral at most `80/(5 - a) + 2 T`, whatever the centre `c`
(`singularIntLe_slab_singularPow`): the local singularity is integrable and the far field is
bounded by `1` on a set of volume `2 T`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The time coordinate is controlled by the square of the parabolic size. -/
theorem abs_fst_le_sq_torusParabolicSize (z : SpaceTime) : |z.1| ≤ torusParabolicSize z ^ 2 := by
  have h1 : √|z.1| ≤ torusParabolicSize z := by
    unfold torusParabolicSize
    linarith [torusSpatialNorm_nonneg z.2]
  have h2 : 0 ≤ √|z.1| := Real.sqrt_nonneg _
  calc |z.1| = √|z.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ torusParabolicSize z ^ 2 := pow_le_pow_left₀ h2 h1 2

theorem measurableSet_abs_fst_le (T : ℝ) : MeasurableSet {w : SpaceTime | |w.1| ≤ T} :=
  measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const

theorem volume_univ_torus3 : volume (Set.univ : Set Torus3) = 1 := by
  unfold Torus3 UnitAddTorus
  rw [volume_pi, Measure.pi_univ]
  simp

theorem volume_abs_fst_le (T : ℝ) :
    volume {w : SpaceTime | |w.1| ≤ T} = ENNReal.ofReal (2 * T) := by
  have : {w : SpaceTime | |w.1| ≤ T} = Set.Icc (-T) T ×ˢ (Set.univ : Set Torus3) := by
    ext w
    simp [abs_le]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, volume_univ_torus3, mul_one]
  congr 1
  ring

/-- A centred power `s(c - w)^(-a)` restricted to the slab `|w.1| ≤ T` is integrable, with
integral at most `80/(5 - a) + 2 T`, uniformly in the centre `c`. -/
theorem singularIntLe_slab_singularPow {a T : ℝ} (ha : 0 < a) (ha5 : a < 5) (hT : 0 ≤ T)
    (c : SpaceTime) :
    SingularIntLe (Set.indicator {w : SpaceTime | |w.1| ≤ T} (singularPow a c))
      (80 / (5 - a) + 2 * T) := by
  have iL := integrable_singularLocalWeight ha ha5 (by norm_num : (0 : ℝ) < 1)
  have iLc := integrable_comp_sub_left_spaceTime iL c
  have hfin : volume {w : SpaceTime | |w.1| ≤ T} < ⊤ := by
    rw [volume_abs_fst_le]
    exact ENNReal.ofReal_lt_top
  have iI : Integrable (Set.indicator {w : SpaceTime | |w.1| ≤ T} (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) hfin.ne).integrable_indicator (measurableSet_abs_fst_le T)
  have hI : ∫ w, Set.indicator {w : SpaceTime | |w.1| ≤ T} (fun _ => (1 : ℝ)) w = 2 * T := by
    rw [integral_indicator_const _ (measurableSet_abs_fst_le T), measureReal_def,
      volume_abs_fst_le, ENNReal.toReal_ofReal (by linarith)]
    simp
  have hf : SingularIntLe (fun w => singularLocalWeight a 1 (c - w) +
      Set.indicator {w : SpaceTime | |w.1| ≤ T} (fun _ => (1 : ℝ)) w) (80 / (5 - a) + 2 * T) := by
    refine ⟨iLc.add iI, ?_⟩
    rw [integral_add iLc iI, integral_comp_sub_left_spaceTime (singularLocalWeight a 1) c, hI]
    have := integral_singularLocalWeight_le ha ha5 (by norm_num : (0 : ℝ) < 1)
    simpa using add_le_add_right this (2 * T)
  refine hf.of_le ?_ ?_ ?_
  · exact ((measurable_singularPow a c).indicator (measurableSet_abs_fst_le T)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w => Set.indicator_nonneg
      (fun w _ => singularPow_nonneg _ _ _) w
  · refine Filter.Eventually.of_forall fun w => ?_
    by_cases hw : w ∈ {w : SpaceTime | |w.1| ≤ T}
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
      have := SemigroupTestProfile.rpow_neg_le_localWeight_add ha (by norm_num : (0 : ℝ) < 1)
        (c - w)
      simpa [singularPow] using this
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      simpa using singularLocalWeight_nonneg a 1 (c - w)

end RegularityStructures

end
