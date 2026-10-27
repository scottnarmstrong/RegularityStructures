/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.MW20.HeatFrechet

/-! Locality of the literal source heat operator, without regularity premises. -/
public section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Filter Topology

 theorem sourceHeat_eq_of_eventuallyEq {f g : ParabolicSpace → ℝ} {p : ParabolicSpace}
    (he : f =ᶠ[𝓝 p] g) : sourceHeat f p = sourceHeat g p := by
  have htime : (fun t : ℝ => f (t, p.2)) =ᶠ[𝓝 p.1] (fun t => g (t, p.2)) := by
    exact ((continuous_id.prodMk continuous_const).continuousAt.tendsto).eventually he
  have hspace (i : Fin 3) :
      (fun a : ℝ => f (p.1, Function.update p.2 i a)) =ᶠ[𝓝 (p.2 i)]
        (fun a => g (p.1, Function.update p.2 i a)) := by
    have hcurve := (hasDerivAt_const (p.2 i) p.1).prodMk (hasDerivAt_update p.2 i (p.2 i))
    have hto := hcurve.continuousAt.tendsto
    have hto' : Tendsto (fun a : ℝ => (p.1, Function.update p.2 i a)) (𝓝 (p.2 i)) (𝓝 p) := by
      simpa only [Function.update_eq_self] using hto
    exact hto'.eventually he
  unfold sourceHeat
  rw [htime.deriv_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (hspace i).deriv.deriv_eq

end GlobalPhi43.Local
