/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.FixedHeatCutoff
public import GlobalPhi43.Local.AnnularHeatExtension

/-! Source-cutoff derivatives and inner targets give one fixed annulus. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric Filter Topology
open scoped ContDiff

 def fixedHeatAnnulus : Set ParabolicSpace := {z | 1 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 1}

 theorem fixedHeatAnnulus_isCompact : IsCompact fixedHeatAnnulus := by
  apply (isCompact_closedBall (0 : ParabolicSpace) 1).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hz.2

 theorem zero_not_mem_fixedHeatAnnulus : (0 : ParabolicSpace) ∉ fixedHeatAnnulus := by
  norm_num [fixedHeatAnnulus]

 theorem fixed_heat_annulus_geometry {χ : ParabolicSpace → ℝ}
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ))
    {p q : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) (hq : q ∈ tsupport χ)
    (houter : q ∉ ball 0 (1 / 2 : ℝ)) : p - q ∈ fixedHeatAnnulus := by
  have hqlo : 1 / 2 ≤ ‖q‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using houter
  have hqhi : ‖q‖ ≤ 3 / 4 := by simpa only [mem_closedBall, dist_zero_right] using hs hq
  have hlo : ‖q‖ - ‖p‖ ≤ ‖p - q‖ := by simpa only [norm_sub_rev] using norm_sub_norm_le q p
  have hhi := norm_sub_le p q
  constructor <;> linarith

/-- The actual kernel and a global smooth compact kernel agree as germs
on every boundary displacement, with all constants chosen before h. -/
theorem exists_fixed_annular_heat_kernel : ∃ k : ParabolicSpace → ℝ,
    ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      (∀ p ∈ fixedHeatAnnulus, k =ᶠ[𝓝 p] heatKernelR4) ∧
      ∃ S ≥ 0, ∀ (x y : ParabolicSpace) (R : ℝ), 0 ≤ R → y ∈ pastBall x R →
        |k y - k x - fderiv ℝ (fun w : Fin 3 → ℝ => k (x.1, w)) x.2 (y.2 - x.2)| ≤
          2 * S * R ^ 2 :=
  annular_heat_kernel_taylor_extension fixedHeatAnnulus_isCompact zero_not_mem_fixedHeatAnnulus

end GlobalPhi43.Local
