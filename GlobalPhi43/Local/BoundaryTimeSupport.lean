/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.BoundaryCausality
public import GlobalPhi43.Local.CutoffInitialGeometry

/-! Boundary source terms vanish outside their fixed retarded time interval. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric Filter Topology

 theorem boundary_integrand_zero_off_time {χ k : ParabolicSpace → ℝ}
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    (he : ∀ z ∈ fixedHeatAnnulus, k =ᶠ[𝓝 z] heatKernelR4)
    {p q : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) (ht : p.1 ≤ 0)
    (hqoff : q.1 ∉ Ioc (-1 : ℝ) p.1) (i : Option (Fin 3)) (b : ℝ) :
    heatBoundaryKernel k i (p - q) * (heatBoundaryCoefficient χ i q * b) = 0 := by
  by_cases hlower : q.1 ≤ -1
  · have hq : q ∉ unitHeatSourceDomain := by
      intro hmem
      exact not_lt_of_ge hlower (unit_source_time_lower hmem)
    exact boundary_integrand_zero_off_unit_domain hs hone he hp ht hq i b
  · have hfuture : p.1 ≤ q.1 := by
      by_contra hh
      exact hqoff ⟨lt_of_not_ge hlower, (lt_of_not_ge hh).le⟩
    exact boundary_integrand_zero_of_future hs hone he hp hfuture i b

end GlobalPhi43.Local
