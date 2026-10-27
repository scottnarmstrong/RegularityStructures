/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatKernelSpatialDerivative
public import GlobalPhi43.Local.BoundaryKernelAgreement
public import GlobalPhi43.Local.UnitHeatSource

/-! Actual boundary kernels vanish outside the fixed past source domain. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric Filter Topology

 theorem heat_kernel_spatial_derivative_zero_of_nonpos {p : ParabolicSpace}
    (ht : p.1 ≤ 0) (hne : p ≠ 0) (v : Fin 3 → ℝ) :
    fderiv ℝ heatKernelR4 p (0, v) = 0 := by
  have hK := (contDiffAt_heatKernelR4 hne).differentiableAt (by simp)
  have hh := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v)
    ((hK.hasFDerivAt.comp p.2 ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv)
  have hz : (fun w : Fin 3 → ℝ => heatKernelR4 (p.1, w)) = fun _ => 0 :=
    funext fun _ => heatKernelR4_of_nonpos ht
  change fderiv ℝ (fun w : Fin 3 → ℝ => heatKernelR4 (p.1, w)) p.2 v =
    fderiv ℝ heatKernelR4 p (0, v) at hh
  rw [hz] at hh
  have hd0 : fderiv ℝ (fun _ : Fin 3 → ℝ => (0 : ℝ)) p.2 = 0 := (hasFDerivAt_const (0 : ℝ) p.2).fderiv
  rw [hd0] at hh
  simpa only [zero_apply] using hh.symm

 theorem boundary_integrand_zero_of_future {χ k : ParabolicSpace → ℝ}
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    (he : ∀ z ∈ fixedHeatAnnulus, k =ᶠ[𝓝 z] heatKernelR4)
    {p q : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) (ht : p.1 ≤ q.1)
    (i : Option (Fin 3)) (b : ℝ) :
    heatBoundaryKernel k i (p - q) * (heatBoundaryCoefficient χ i q * b) = 0 := by
  by_cases hz : heatBoundaryCoefficient χ i q = 0
  · simp [hz]
  · obtain ⟨hq, hout⟩ := boundary_coefficient_support hone i hz
    have hA := fixed_heat_annulus_geometry hs hp hq hout
    have hne : p - q ≠ 0 := fun hh => zero_not_mem_fixedHeatAnnulus (hh ▸ hA)
    have htime : (p - q).1 ≤ 0 := by change p.1 - q.1 ≤ 0; linarith
    rw [boundary_kernel_agreement hs hone he hp i hz]
    cases i with
    | none => simp [heatBoundaryKernel, heatKernelR4_of_nonpos htime]
    | some j => simp [heatBoundaryKernel, heat_kernel_spatial_derivative_zero_of_nonpos htime hne]

 theorem boundary_integrand_zero_off_unit_domain {χ k : ParabolicSpace → ℝ}
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    (he : ∀ z ∈ fixedHeatAnnulus, k =ᶠ[𝓝 z] heatKernelR4)
    {p q : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) (ht : p.1 ≤ 0)
    (hqoff : q ∉ unitHeatSourceDomain) (i : Option (Fin 3)) (b : ℝ) :
    heatBoundaryKernel k i (p - q) * (heatBoundaryCoefficient χ i q * b) = 0 := by
  by_cases hz : heatBoundaryCoefficient χ i q = 0
  · simp [hz]
  · have hq := (boundary_coefficient_support hone i hz).1
    have hnorm : ‖q‖ ≤ 3 / 4 := by simpa only [mem_closedBall, dist_zero_right] using hs hq
    have hball : q ∈ ball (0 : ParabolicSpace) 1 := by rw [mem_ball, dist_zero_right]; linarith
    have hqtime : 0 ≤ q.1 := by
      by_contra hh
      exact hqoff ⟨hball, lt_of_not_ge hh⟩
    exact boundary_integrand_zero_of_future hs hone he hp (ht.trans hqtime) i b

end GlobalPhi43.Local
