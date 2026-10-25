/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesZero
public import RegularityStructures.Abstract.Singular.TaylorKernel.ProfileSupOn
public import RegularityStructures.Analysis.Heat.Schauder.ConvolutionLineIter

/-!
# The Taylor-remainder kernel at scale `n = 0`, window models

Window (`_win`) versions of the model-dependent statements of
`RegularityStructures.Abstract.Singular.KGamma.SeriesZero` (`exists_dTaylor_zero_data` is model-free
and reused): the window layer bound for test functions supported in `B(x, 2)` and the model pairing
bound for the kernel at scale `0`.

The model pairing bound is proved without test functions of radius `2`, which would require the
model outside the window.  Instead `⟨Π_x e_i, K^{k,σ}_{0;yx}⟩` is the limit of the regularised
pairings, and each of these is the Taylor remainder, at `x` and for the increment `y − x`, of the
smooth function `z ↦ ∫ Q_s Π_x e_i (w) D^k K_0(z − w) dw`.  The derivatives of this function at
the points `z` of the coordinate box between `x` and `y` (which lie in the slab) are regularised
pairings with unit test functions centred at `z`, bounded uniformly in `s` by the off-centre bound
`exists_abs_pairing_regPi_single_offcentre_le_win`; the localised Taylor bound
`exists_abs_taylorProfile_le_sup_on` then gives `C K₀ d^σ`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

/-- A smooth function vanishing outside the unit ball is a unit scaled test function at every
centre, with a constant independent of the centre. -/
theorem exists_isScaledTest_unit_of_contDiff {G : ParabolicSpace → ℝ} (hG : ContDiff ℝ ∞ G)
    (h0 : ∀ w, 1 < parabolicNorm w → G w = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ z, IsScaledTest (fun y => G (z - y)) z 1 A := by
  have hGs : ContDiff ℝ ∞ (fun v => G (-v)) := hG.comp contDiff_neg
  have hG0 : HasCompactSupport (fun v => G (-v)) :=
    hasCompactSupport_of_eq_zero_unit fun w hw => h0 _ (by rwa [parabolicNorm_neg])
  obtain ⟨C₀, hC₀, hC⟩ := hG0.exists_bound_iteratedFDeriv hGs 4
  refine ⟨C₀ + 1, by linarith, fun z => ?_⟩
  refine ⟨hG.comp (contDiff_const.sub contDiff_id), one_pos, le_rfl, by linarith,
    fun w hw => ?_, fun i hi v => ?_⟩
  · refine h0 _ ?_
    rwa [parabolicNorm_sub_comm] at hw
  · have e : (fun v => G (z - (z + parabolicDilate 1 v))) = fun v => G (-v) := by
      funext v; simp [parabolicDilate_one]
    rw [e]
    exact (hC i hi v).trans (by linarith)

/-- A measurable function of polynomial growth is locally integrable. -/
theorem locallyIntegrable_of_polyGrowth {f : ParabolicSpace → ℝ} (hf : Measurable f)
    {x : ParabolicSpace} {C q : ℝ} (hq : 0 ≤ q)
    (hb : ∀ w, |f w| ≤ C * (1 + parabolicNorm (w - x)) ^ q) : LocallyIntegrable f := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hc : Continuous fun w : ParabolicSpace => parabolicNorm (w - x) :=
    continuous_parabolicNorm.comp (continuous_id.sub continuous_const)
  obtain ⟨R, hR⟩ := (hK.image hc).bddAbove
  refine Measure.integrableOn_of_bounded (M := |C| * (1 + R) ^ q) hK.measure_lt_top.ne
    hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Filter.Eventually.of_forall fun w hw => ?_)
  have hwR : parabolicNorm (w - x) ≤ R := hR ⟨w, hw, rfl⟩
  rw [Real.norm_eq_abs]
  refine (hb w).trans ?_
  have h1 : (1 + parabolicNorm (w - x)) ^ q ≤ (1 + R) ^ q :=
    Real.rpow_le_rpow (by linarith [parabolicNorm_nonneg (w - x)]) (by linarith) hq
  have hb1 : 0 ≤ 1 + parabolicNorm (w - x) := by linarith [parabolicNorm_nonneg (w - x)]
  calc C * (1 + parabolicNorm (w - x)) ^ q ≤ |C| * (1 + parabolicNorm (w - x)) ^ q :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hb1 _)
    _ ≤ |C| * (1 + R) ^ q := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem boxPt_fst (s τ : Fin 4 → ℝ) : (boxPt s τ).1 = τ 0 * s 0 := by
  simp [boxPt, Fin.sum_univ_succ, coordDir, timeDir, spaceDir]

theorem boxPt_snd (s τ : Fin 4 → ℝ) (a : Fin 3) : (boxPt s τ).2 a = τ a.succ * s a.succ := by
  fin_cases a <;> simp [boxPt, Fin.sum_univ_succ, coordDir, timeDir, spaceDir]

theorem parabolicNorm_boxPt_le (z : ParabolicSpace) {τ : Fin 4 → ℝ}
    (hτ : ∀ j, 0 ≤ τ j ∧ τ j ≤ 1) : parabolicNorm (boxPt (parabolicCoords z) τ) ≤ parabolicNorm z := by
  unfold parabolicNorm
  have h1 : |(boxPt (parabolicCoords z) τ).1| ≤ |z.1| := by
    rw [boxPt_fst, abs_mul, abs_of_nonneg (hτ 0).1]
    have : parabolicCoords z 0 = z.1 := by simp [parabolicCoords]
    rw [this]
    exact mul_le_of_le_one_left (abs_nonneg _) (hτ 0).2
  have h2 : ∀ a : Fin 3, |(boxPt (parabolicCoords z) τ).2 a| ≤ |z.2 a| := by
    intro a
    rw [boxPt_snd, abs_mul, abs_of_nonneg (hτ a.succ).1]
    have : parabolicCoords z a.succ = z.2 a := by fin_cases a <;> simp [parabolicCoords]
    rw [this]
    exact mul_le_of_le_one_left (abs_nonneg _) (hτ a.succ).2
  exact add_le_add (Real.sqrt_le_sqrt h1) (Finset.sum_le_sum fun a _ => h2 a)

end RegularityStructures

end
