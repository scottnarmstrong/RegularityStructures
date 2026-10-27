/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.FixedBoundaryAffineBound
public import GlobalPhi43.Local.HeatGeneratorGerm

/-! The compact annular kernel is an internal proof device: its actual
boundary potential agrees with the ordinary heat kernel on the inner core. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric Filter Topology MeasureTheory

 theorem boundary_coefficient_zero_of_germ_constant {χ : ParabolicSpace → ℝ}
    {p : ParabolicSpace} {c : ℝ} (he : χ =ᶠ[𝓝 p] (fun _ => c)) (i : Option (Fin 3)) :
    heatBoundaryCoefficient χ i p = 0 := by
  cases i with
  | none =>
    change heatTestGenerator χ p = 0
    rw [heatTestGenerator_eq_of_eventuallyEq he]
    simp [heatTestGenerator]
  | some i =>
    have hd : fderiv ℝ χ p = 0 := by simpa using he.fderiv_eq (𝕜 := ℝ)
    simp [heatBoundaryCoefficient, hd]

 theorem boundary_coefficient_support {χ : ParabolicSpace → ℝ}
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    (i : Option (Fin 3)) {q : ParabolicSpace} (hne : heatBoundaryCoefficient χ i q ≠ 0) :
    q ∈ tsupport χ ∧ q ∉ ball 0 (1 / 2 : ℝ) := by
  constructor
  · by_contra hq
    have he : χ =ᶠ[𝓝 q] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hq] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    exact hne (boundary_coefficient_zero_of_germ_constant he i)
  · intro hq
    exact hne (boundary_coefficient_zero_of_germ_constant (fixed_cutoff_inner_germ hone hq) i)

 theorem boundary_kernel_agreement {χ k : ParabolicSpace → ℝ}
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    (he : ∀ z ∈ fixedHeatAnnulus, k =ᶠ[𝓝 z] heatKernelR4)
    {p q : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) (i : Option (Fin 3))
    (hne : heatBoundaryCoefficient χ i q ≠ 0) :
    heatBoundaryKernel k i (p - q) = heatBoundaryKernel heatKernelR4 i (p - q) := by
  obtain ⟨hq, hout⟩ := boundary_coefficient_support hone i hne
  have hgem := he (p - q) (fixed_heat_annulus_geometry hs hp hq hout)
  cases i with
  | none => exact hgem.self_of_nhds
  | some i => exact congrArg (fun L : ParabolicSpace →L[ℝ] ℝ => L (0, Pi.single i 1)) hgem.fderiv_eq

 theorem heatBoundaryPotential_agreement {χ k : ParabolicSpace → ℝ}
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    (hone : ∀ p ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ p = 1)
    (he : ∀ z ∈ fixedHeatAnnulus, k =ᶠ[𝓝 z] heatKernelR4)
    (μ : Measure ParabolicSpace) (g : ParabolicSpace → ℝ) {p : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) :
    heatBoundaryPotential k χ μ g p = heatBoundaryPotential heatKernelR4 χ μ g p := by
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  apply ae_of_all
  intro q
  dsimp only
  by_cases hz : heatBoundaryCoefficient χ i q = 0
  · simp only [hz, zero_mul, mul_zero]
  · rw [boundary_kernel_agreement hs hone he hp i hz]

end GlobalPhi43.Local
