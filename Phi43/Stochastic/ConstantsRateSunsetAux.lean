/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateCorr
public import Phi43.Stochastic.ConstantsRateMollifyKernels
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Auxiliary Hölder estimates for the second-constant comparison

A bounded `L^{3/2}` function is in `L³`; a three-fold Hölder inequality `3 · 3 · 3`; a Hölder
inequality with a bounded weight; and the bilinear splitting of a difference of correlations.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_memLp_three_of_bounded {f : SpaceTime → ℝ}
    (hf : MemLp f (ENNReal.ofReal (3 / 2))) {C : ℝ} (hC : ∀ z, |f z| ≤ C) :
    MemLp f (ENNReal.ofReal 3) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hfin := constantsRate_lintegral_ne_top (by norm_num : (0 : ℝ) < 3 / 2) hf
  have hint : ∫⁻ z, ‖f z‖ₑ ^ (3 : ℝ) ≠ ⊤ := by
    have hpt : ∀ z, ‖f z‖ₑ ^ (3 : ℝ) ≤
        ENNReal.ofReal C ^ (3 / 2 : ℝ) * ‖f z‖ₑ ^ (3 / 2 : ℝ) := by
      intro z
      have h1 : ‖f z‖ₑ ≤ ENNReal.ofReal C := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hC z)
      calc
        ‖f z‖ₑ ^ (3 : ℝ) = ‖f z‖ₑ ^ (3 / 2 : ℝ) * ‖f z‖ₑ ^ (3 / 2 : ℝ) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
          norm_num
        _ ≤ ENNReal.ofReal C ^ (3 / 2 : ℝ) * ‖f z‖ₑ ^ (3 / 2 : ℝ) := by
          gcongr
    refine ne_of_lt ((lintegral_mono hpt).trans_lt ?_)
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top)]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top) hfin.lt_top
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr (by norm_num)).ne' ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
  simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3)] using hint.lt_top

/-- Hölder `3 + 3/2 = 1`. -/
theorem constantsRate_enorm_integral_mul_le' {f g : SpaceTime → ℝ}
    (hf : MemLp f (ENNReal.ofReal 3)) (hg : MemLp g (ENNReal.ofReal (3 / 2))) :
    ‖∫ z, f z * g z‖ₑ ≤
      eLpNorm f (ENNReal.ofReal 3) volume * eLpNorm g (ENNReal.ofReal (3 / 2)) volume := by
  have := (constantsRate_corr_bound constantsRate_holder_three hf hg 0).2
  simpa only [zero_add] using this

/-- `3 · 3 · 3` Hölder for three `L³` functions. -/
theorem constantsRate_enorm_integral_mul_three_le {f g h : SpaceTime → ℝ}
    (hf : MemLp f (ENNReal.ofReal 3)) (hg : MemLp g (ENNReal.ofReal 3))
    (hh : MemLp h (ENNReal.ofReal 3)) :
    ‖∫ z, f z * (g z * h z)‖ₑ ≤
      eLpNorm f (ENNReal.ofReal 3) volume * (eLpNorm g (ENNReal.ofReal 3) volume *
        eLpNorm h (ENNReal.ofReal 3) volume) := by
  have hT : (ENNReal.ofReal 3).HolderTriple (ENNReal.ofReal 3) (ENNReal.ofReal (3 / 2)) := by
    constructor
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have hgh : MemLp (g * h) (ENNReal.ofReal (3 / 2)) := hg.mul hh
  have h1 := constantsRate_enorm_integral_mul_le' hf hgh
  refine h1.trans (mul_le_mul' le_rfl ?_)
  exact eLpNorm_smul_le_mul_eLpNorm hg.aestronglyMeasurable hh.aestronglyMeasurable

theorem constantsRate_corr_sub_eq {u u' v v' : SpaceTime → ℝ} {z : SpaceTime}
    (h1 : Integrable (fun w => u' (z + w) * v' w)) (h2 : Integrable (fun w => u (z + w) * v w))
    (h3 : Integrable (fun w => (u' (z + w) - u (z + w)) * v' w))
    (h4 : Integrable (fun w => u (z + w) * (v' w - v w))) :
    constantsRateCorr u' v' z - constantsRateCorr u v z =
      constantsRateCorr (fun x => u' x - u x) v' z +
        constantsRateCorr u (fun x => v' x - v x) z := by
  unfold constantsRateCorr
  rw [← integral_sub h1 h2, ← integral_add h3 h4]
  apply integral_congr_ae
  filter_upwards [] with w
  ring

/-- Difference of two `(L³, L^{3/2})` correlations, at every point. -/
theorem constantsRate_corr_diff_bound {a a' b b' : SpaceTime → ℝ}
    (ha : MemLp a (ENNReal.ofReal 3)) (ha' : MemLp a' (ENNReal.ofReal 3))
    (hb : MemLp b (ENNReal.ofReal (3 / 2))) (hb' : MemLp b' (ENNReal.ofReal (3 / 2)))
    (z : SpaceTime) :
    ‖constantsRateCorr a' b' z - constantsRateCorr a b z‖ₑ ≤
      eLpNorm (fun x => a' x - a x) (ENNReal.ofReal 3) volume *
          eLpNorm b' (ENNReal.ofReal (3 / 2)) volume +
        eLpNorm a (ENNReal.ofReal 3) volume *
          eLpNorm (fun x => b' x - b x) (ENNReal.ofReal (3 / 2)) volume := by
  have hH := constantsRate_holder_three
  have e := constantsRate_corr_sub_eq (u := a) (u' := a') (v := b) (v' := b') (z := z)
    (constantsRate_corr_bound hH ha' hb' z).1 (constantsRate_corr_bound hH ha hb z).1
    (constantsRate_corr_bound hH (ha'.sub ha) hb' z).1
    (constantsRate_corr_bound hH ha (hb'.sub hb) z).1
  rw [e]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (constantsRate_corr_bound hH (ha'.sub ha) hb' z).2
  · exact (constantsRate_corr_bound hH ha (hb'.sub hb) z).2

/-- Difference of two `(L^{3/2}, L³)` correlations, at every point. -/
theorem constantsRate_corr_diff_bound' {a a' b b' : SpaceTime → ℝ}
    (ha : MemLp a (ENNReal.ofReal (3 / 2))) (ha' : MemLp a' (ENNReal.ofReal (3 / 2)))
    (hb : MemLp b (ENNReal.ofReal 3)) (hb' : MemLp b' (ENNReal.ofReal 3))
    (z : SpaceTime) :
    ‖constantsRateCorr a' b' z - constantsRateCorr a b z‖ₑ ≤
      eLpNorm (fun x => a' x - a x) (ENNReal.ofReal (3 / 2)) volume *
          eLpNorm b' (ENNReal.ofReal 3) volume +
        eLpNorm a (ENNReal.ofReal (3 / 2)) volume *
          eLpNorm (fun x => b' x - b x) (ENNReal.ofReal 3) volume := by
  have hH := constantsRate_holder_three_halves
  have e := constantsRate_corr_sub_eq (u := a) (u' := a') (v := b) (v' := b') (z := z)
    (constantsRate_corr_bound hH ha' hb' z).1 (constantsRate_corr_bound hH ha hb z).1
    (constantsRate_corr_bound hH (ha'.sub ha) hb' z).1
    (constantsRate_corr_bound hH ha (hb'.sub hb) z).1
  rw [e]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (constantsRate_corr_bound hH (ha'.sub ha) hb' z).2
  · exact (constantsRate_corr_bound hH ha (hb'.sub hb) z).2

/-- Weighted Hölder in `lintegral` form, with an almost-everywhere bounded weight. -/
theorem constantsRate_lintegral_weight_le {a f g : SpaceTime → ℝ} {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (ha : ∀ᵐ z : SpaceTime ∂volume, ‖a z‖ₑ ≤ B) (hf : MemLp f (ENNReal.ofReal (3 / 2)))
    (hg : MemLp g (ENNReal.ofReal 3)) :
    ∫⁻ z, ‖a z * (f z * g z)‖ₑ ≤
      B * (eLpNorm f (ENNReal.ofReal (3 / 2)) volume * eLpNorm g (ENNReal.ofReal 3) volume) := by
  have hT : (ENNReal.ofReal (3 / 2)).HolderTriple (ENNReal.ofReal 3) 1 :=
    constantsRate_holder_three_halves.ennrealOfReal
  have hfg : AEStronglyMeasurable (fun z => f z * g z) volume :=
    hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  calc
    ∫⁻ z, ‖a z * (f z * g z)‖ₑ ≤ ∫⁻ z, B * ‖f z * g z‖ₑ := by
      apply lintegral_mono_ae
      filter_upwards [ha] with z hz
      rw [enorm_mul]
      exact mul_le_mul' hz le_rfl
    _ = B * ∫⁻ z, ‖f z * g z‖ₑ := lintegral_const_mul' _ _ hB
    _ = B * eLpNorm (fun z => f z * g z) 1 volume := by
      rw [eLpNorm_one_eq_lintegral_enorm hfg]
    _ ≤ B * (eLpNorm f (ENNReal.ofReal (3 / 2)) volume * eLpNorm g (ENNReal.ofReal 3) volume) :=
      mul_le_mul' le_rfl (eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable
        hg.aestronglyMeasurable)

theorem constantsRate_eLpNorm_add_le {f g : SpaceTime → ℝ} {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun z => f z + g z) (ENNReal.ofReal p) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume + eLpNorm g (ENNReal.ofReal p) volume :=
  eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)

theorem constantsRate_norm_le_of_enorm_le {x : ℝ} {B : ℝ≥0∞} (hB : B ≠ ⊤) (h : ‖x‖ₑ ≤ B) :
    ‖x‖ ≤ B.toReal := by
  have h2 := ENNReal.toReal_mono hB h
  rwa [toReal_enorm] at h2

end RegularityStructures.Phi43

end
