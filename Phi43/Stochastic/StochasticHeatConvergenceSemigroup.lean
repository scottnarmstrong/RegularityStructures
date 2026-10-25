/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelTorusConvolution
public import RegularityStructures.Torus.KolmogorovHolderBesovHeat

/-!
# Spatial heat convolution of the massive kernel

The spatial heat semigroup can be evaluated explicitly on a positive-time massive heat kernel.
This is the deterministic reduction used below when time differences are estimated after spatial
heat regularisation.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem integral_heatKernel_mul_massiveHeatKernel_torus
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Torus3) :
    ∫ y : Torus3, heatKernel s y * massiveHeatKernel (t, x - y) =
      exp (-t) * heatKernel (s + t) x := by
  have htorus : ∫ y : Torus3, heatKernel s y * heatKernel t (x - y) =
      heatKernel (s + t) x := by
    calc
      ∫ y : Torus3, heatKernel s y * heatKernel t (x - y) =
          heatSemigroup s ⟨heatKernel t, continuous_heatKernel_fixed ht⟩ x := by
        symm
        simpa using heatSemigroup_eq_torus_integral hs
          ⟨heatKernel t, continuous_heatKernel_fixed ht⟩ x
      _ = heatKernel (s + t) x := heatSemigroup_heatKernel hs ht x
  simp only [massiveHeatKernel, ht, ite_true]
  calc
    ∫ y : Torus3, heatKernel s y * (exp (-t) * heatKernel t (x - y)) =
        ∫ y : Torus3, exp (-t) *
          (heatKernel s y * heatKernel t (x - y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = exp (-t) * ∫ y : Torus3,
        heatKernel s y * heatKernel t (x - y) := by
      rw [integral_const_mul]
    _ = exp (-t) * heatKernel (s + t) x := by rw [htorus]

end RegularityStructures.Phi43

end
