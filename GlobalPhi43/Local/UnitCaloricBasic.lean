/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitCutoffHeatRepresentation
public import GlobalPhi43.Local.UnitBoundaryAffineBound
public import GlobalPhi43.Local.LocalCutoffForcing
public import GlobalPhi43.Local.AffineErrorComparison

/-! The genuine ordinary-heat unit-box affine estimate before subtracting
an affine comparison. Only local past field/PDE suprema enter the bound. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric Filter Topology MeasureTheory
open scoped ContDiff ENNReal

 theorem exists_unit_caloric_basic : ∃ C > 0,
    ∀ (h : ParabolicSpace → ℝ) (O : Set ParabolicSpace), IsOpen O →
      unitHeatPastCarrier ⊆ O → ContDiffOn ℝ ∞ h O →
      ∀ (H F : ℝ), 0 ≤ H → 0 ≤ F →
      (∀ p ∈ pastBall (0 : ParabolicSpace) 1, |h p| ≤ H) →
      (∀ p ∈ pastBall (0 : ParabolicSpace) 1, |sourceHeat h p| ≤ F) →
      ∀ R : ℝ, 0 ≤ R → R ≤ 1 / 4 →
        pastAffineError h 0 R ≤ ENNReal.ofReal (C * (H * R ^ 2 + F)) := by
  obtain ⟨χ, C, hχ, hcχ, hrange, hs, hone, hC, hboundary⟩ := exists_unit_boundary_affine_bound
  refine ⟨1 + C, by linarith, ?_⟩
  intro h O hO hKO hh H F hH hF hHb hPDE R hR hRsmall
  obtain ⟨g, hg, _, he, hBE⟩ := hboundary h O hO hKO hh H hH hHb
  have hclose : ∀ y ∈ pastBall (0 : ParabolicSpace) R,
      |h y - heatBoundaryPotential heatKernelR4 χ unitHeatSourceMeasure g y| ≤ F := by
    intro y hy
    have hnorm := small_pastBall_norm_le hR hRsmall hy
    have hytime : y.1 < 0 := hy.2
    have hyK : y ∈ unitHeatPastCarrier := by
      constructor
      · rw [mem_closedBall, dist_zero_right]
        linarith
      · exact hytime.le
    have hvalue := (he y hyK).self_of_nhds
    have hrepr := unit_cutoff_heat_representation hχ hcχ hg hs hone hnorm hytime.le
    have hT : 0 ≤ y.1 + 1 := by linarith [unit_core_time_lower hnorm]
    have hforce := local_cutoff_forcing_potential_bound hχ hcχ hrange hs hg he hF hytime.le hT hPDE y.2
    have heq : h y - heatBoundaryPotential heatKernelR4 χ unitHeatSourceMeasure g y =
        ∫ s in (0 : ℝ)..(y.1 + 1), ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) *
          (χ (y.1 - s, y.2 - w) * sourceHeat g (y.1 - s, y.2 - w)) := by
      linarith only [hvalue, hrepr]
    rw [heq]
    exact hforce.2.trans (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hytime.le hF])
  have happrox := pastAffineError_le_of_close h (heatBoundaryPotential heatKernelR4 χ unitHeatSourceMeasure g) 0 hclose
  have hmain := happrox.trans (add_le_add (hBE R hR hRsmall) le_rfl)
  have hterm : 0 ≤ C * H * R ^ 2 := mul_nonneg (mul_nonneg hC.le hH) (sq_nonneg R)
  rw [← ENNReal.ofReal_add hterm hF] at hmain
  apply hmain.trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [mul_nonneg hH (sq_nonneg R), mul_nonneg hC.le hF]

end GlobalPhi43.Local
