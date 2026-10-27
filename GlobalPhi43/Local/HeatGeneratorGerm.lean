/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatTestGenerator

/-! Germ locality of the explicit adjoint heat generator. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Filter Topology

 theorem heatTestGenerator_eq_of_eventuallyEq {f g : ParabolicSpace → ℝ} {p : ParabolicSpace}
    (he : f =ᶠ[𝓝 p] g) : heatTestGenerator f p = heatTestGenerator g p := by
  unfold heatTestGenerator
  rw [he.fderiv_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hg : (fun q : ParabolicSpace => fderiv ℝ f q (0, Pi.single i 1)) =ᶠ[𝓝 p]
      (fun q : ParabolicSpace => fderiv ℝ g q (0, Pi.single i 1)) :=
    (he.fderiv (𝕜 := ℝ)).mono fun q hq => congrArg (fun L : ParabolicSpace →L[ℝ] ℝ => L (0, Pi.single i 1)) hq
  rw [hg.fderiv_eq]

end GlobalPhi43.Local
