/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatOperatorRegularity
public import GlobalPhi43.MW20.Setting.HeatOperator

/-! Germ locality of the Fréchet heat operator and its exact agreement
with the native source heat on smooth fields. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Filter Topology
open scoped ContDiff

 theorem heatOperator_eq_of_eventuallyEq {f g : ParabolicSpace → ℝ} {z : ParabolicSpace}
    (he : f =ᶠ[𝓝 z] g) : heatOperator f z = heatOperator g z := by
  have hd := he.fderiv (𝕜 := ℝ)
  unfold heatOperator
  rw [hd.self_of_nhds]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun w => fderiv ℝ f w (0, Pi.single i 1)) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ g w (0, Pi.single i 1)) := by
    filter_upwards [hd] with w hw
    rw [hw]
  rw [(hi.fderiv (𝕜 := ℝ)).self_of_nhds]

 theorem sourceHeat_eq_heatOperator {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : ParabolicSpace) : sourceHeat f z = heatOperator f z := by
  rw [sourceHeat_eq_testGenerator hf]
  unfold heatTestGenerator heatOperator
  ring

end GlobalPhi43.Local
