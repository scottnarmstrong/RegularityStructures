/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceSemigroup
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Reflection and the spatial covariance convolution

The periodised Gaussian is invariant under reflection. Combined with the heat semigroup
identity, this evaluates the spatial integral of the two kernel factors in the bare covariance.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem gaussKernel_neg_local (t : ℝ) (y : Fin 3 → ℝ) :
    gaussKernel t (-y) = gaussKernel t y := by
  simp only [gaussKernel, sqNorm3, Pi.neg_apply, neg_sq]

private theorem heatKernelLift_neg_local (t : ℝ) (y : Fin 3 → ℝ) :
    heatKernelLift t (-y) = heatKernelLift t y := by
  unfold heatKernelLift
  conv_lhs => rw [← (Equiv.neg (Fin 3 → ℤ)).tsum_eq]
  apply tsum_congr
  intro k
  have harg : (fun i => (-y) i + (((Equiv.neg (Fin 3 → ℤ)) k) i : ℝ)) =
      -(fun i => y i + (k i : ℝ)) := by
    funext i
    simp only [Equiv.neg_apply, Pi.neg_apply, Int.cast_neg]
    ring
  rw [harg, gaussKernel_neg_local]

theorem heatKernel_neg (t : ℝ) (x : Torus3) : heatKernel t (-x) = heatKernel t x := by
  let y : Fin 3 → ℝ := torusRep x
  have hy : torusProj y = x := by
    funext i
    simp only [y, torusProj, torusRep]
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x i)
  have hny : torusProj (-y) = -x := by
    rw [← hy]
    funext i
    simp only [torusProj, Pi.neg_apply]
    exact map_neg (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (y i)
  rw [← hny, ← hy, heatKernel_comp_torusProj_eq_lift,
    heatKernel_comp_torusProj_eq_lift, heatKernelLift_neg_local]

theorem integral_heatKernel_mul_heatKernel_add {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (x : Torus3) :
    ∫ y : Torus3, heatKernel s y * heatKernel t (x + y) =
      heatKernel (s + t) x := by
  have hreflect := integral_neg_eq_self (μ := (volume : Measure Torus3))
    (fun y : Torus3 => heatKernel s y * heatKernel t (x - y))
  have hsub : ∫ y : Torus3, heatKernel s y * heatKernel t (x - y) =
      heatKernel (s + t) x := by
    have h := integral_heatKernel_mul_massiveHeatKernel_torus hs ht x
    simp only [massiveHeatKernel, ht, ite_true] at h
    have hfactor :
        (fun y : Torus3 => heatKernel s y * (exp (-t) * heatKernel t (x - y))) =
          (fun y => exp (-t) * (heatKernel s y * heatKernel t (x - y))) := by
      funext y
      ring
    rw [hfactor, integral_const_mul] at h
    exact mul_left_cancel₀ (exp_ne_zero _) h
  simpa only [heatKernel_neg, sub_neg_eq_add, hsub] using hreflect

end RegularityStructures.Phi43

end
