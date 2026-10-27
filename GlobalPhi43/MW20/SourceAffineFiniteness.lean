module

public import GlobalPhi43.MW20.SmoothAffineFiniteness
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.MW20.LocalSourcePairNorms

/-!
# Standing smoothness discharges source affine norm finiteness
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Every actual mixed source interior lies in the fixed compact unit ball. -/
theorem mixedInterior_subset_unit_closedBall {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) :
    Local.cylinderInterior r d ⊆ Metric.closedBall (0 : ParabolicSpace) 1 := by
  intro z hz
  have hzP : z ∈ sourceCylinder 0 :=
    sourceCylinder_antitone (by norm_num) hr (mixedInterior_subset_base hd hz)
  have ht : |z.1| ≤ 1 := abs_le.mpr ⟨by linarith [hzP.1], hzP.2.1.le⟩
  have hs : ‖z.2‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    simpa only [Real.norm_eq_abs, sub_zero] using (hzP.2.2 i).le
  simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using max_le ht hs


/-- Every actual radius-local source affine norm is finite, with no
supplied Schauder bound or independent coefficient/finite-norm premise. -/
theorem source_expansion_radiusAffine_ne_top
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d γ : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (L : ℝ) :
    radiusAffineSeminorm (sourceExpansion v Y Z) (Local.cylinderInterior r d) γ L ≠ ⊤ := by
  apply radiusAffineSeminorm_ne_top_of_smooth (sourceExpansion v Y Z)
    (sourceExpansion_contDiff v Y Z hv hY hZ) _ 1
    (mixedInterior_subset_unit_closedBall hr hd) hγ hγ2 ?_ L
  intro x _
  exact Local.expansion_diag v Y Z x

end GlobalPhi43.MW20
