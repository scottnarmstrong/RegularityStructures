/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonYoung
public import RegularityStructures.Probability.SpaceTimeMeasure
import Mathlib.MeasureTheory.Integral.Prod
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# An `Lᵖ` form of the signed Young estimate

The comparison of the constants applies the signed Young bound to a function already known to have
an integrable `p`-th power.  This module supplies the product-measure input without assuming a sign
for the kernel.  The change of variables is the Haar-measure shear
`(x, y) ↦ (x - y, y)` on `ℝ × T³`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace RegularityStructures.Phi43

theorem constantsComparison_spaceTimeConvolution_integral_rpow_le
    {k f : SpaceTime → ℝ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hk : Measurable k) (hki : Integrable k) (hf : Measurable f)
    (hfp : Integrable (fun z : SpaceTime => |f z| ^ p))
    (hconv : ∀ᵐ x ∂(volume : Measure SpaceTime),
      Integrable (fun y => k y * f (x - y))) :
    Integrable (fun x => |spaceTimeConvolution k f x| ^ p) ∧
      ∫ x, |spaceTimeConvolution k f x| ^ p ≤
        (∫ y, |k y|) ^ (p - 1) *
          (∫ y, |k y|) * ∫ x, |f x| ^ p := by
  have hbase : Integrable (fun z : SpaceTime × SpaceTime =>
      |f z.1| ^ p * |k z.2|)
      ((volume : Measure SpaceTime).prod volume) := by
    exact hfp.mul_prod hki.norm
  have hshear : MeasurePreserving
      (fun z : SpaceTime × SpaceTime => (z.1 - z.2, z.2))
      ((volume : Measure SpaceTime).prod volume)
      ((volume : Measure SpaceTime).prod volume) :=
    measurePreserving_sub_prod (μ := (volume : Measure SpaceTime))
      (ν := (volume : Measure SpaceTime))
  have hweighted' := hshear.integrable_comp_of_integrable hbase
  have hweighted : Integrable (fun z : SpaceTime × SpaceTime =>
      |k z.2| * |f (z.1 - z.2)| ^ p)
      ((volume : Measure SpaceTime).prod volume) := by
    simpa only [Function.comp_def, Prod.fst, Prod.snd, mul_comm] using hweighted'
  obtain ⟨hconvLp, hbound⟩ := constantsComparison_spaceTimeConvolution_Lp_integrable
    hpq hk hki hf hconv hweighted
  have hprod :
      ∫ z : SpaceTime × SpaceTime, |k z.2| * |f (z.1 - z.2)| ^ p =
        (∫ y, |k y|) * ∫ x, |f x| ^ p := by
    rw [Measure.volume_eq_prod SpaceTime SpaceTime]
    rw [integral_prod _ hweighted]
    rw [integral_integral_swap hweighted]
    calc
      (∫ y, ∫ x, |k y| * |f (x - y)| ^ p) =
          ∫ y, |k y| * ∫ x, |f (x - y)| ^ p := by
        apply integral_congr_ae
        filter_upwards [hweighted.prod_left_ae] with y hy
        rw [integral_const_mul]
      _ = ∫ y, |k y| * ∫ x, |f x| ^ p := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [show (fun x : SpaceTime => |f (x - y)| ^ p) =
            (fun x => |f (-y + x)| ^ p) by
              funext x
              simp [sub_eq_add_neg, add_comm]]
        have hshift := integral_comp_add_left_spaceTime
          (fun x : SpaceTime => |f x| ^ p) (-y)
        rw [hshift]
      _ = (∫ y, |k y|) * ∫ x, |f x| ^ p := by
        rw [integral_mul_const]
  refine ⟨hconvLp, ?_⟩
  rw [hprod] at hbound
  simpa only [mul_assoc] using hbound

end RegularityStructures.Phi43

end
