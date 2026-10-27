module

public import GlobalPhi43.Local.SmallScaleSmoothLocalization
public import GlobalPhi43.Local.SmallScaleNormCongruence
public import GlobalPhi43.Local.CylinderClosure
public import GlobalPhi43.MW20.Setting.IsMWLocalData
public import GlobalPhi43.MW20.Setting.IsMWTestKernel

public section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff

/-- The local-data cylinder and the source cylinder have exactly the same carrier. -/
theorem mwCylinder_eq_sourceCylinder : mwCylinder = sourceCylinder 0 := by
  rw [sourceCylinder_zero_eq_prod]
  simp only [mwCylinder, Metric.ball, dist_zero_right]

theorem isCompact_closure_mwCylinder : IsCompact (closure mwCylinder) := by
  rw [mwCylinder_eq_sourceCylinder, closure_sourceCylinder_zero]
  exact isCompact_Icc

/-- Admissible test profiles satisfy the native kernel interface. -/
theorem kernelProfile_of_isMWTestKernel {Φ : ParabolicSpace → ℝ}
    (h : IsMWTestKernel Φ) : KernelProfile Φ := by
  have hs : tsupport Φ ⊆ kernelPastUnitBall := by
    intro z hz
    have hp := h.2.1 hz
    change max (Real.sqrt |(0 : ℝ)-z.1|) ‖(0 : Fin 3 → ℝ)-z.2‖ < 1 ∧ z.1 < 0 at hp
    have ht : Real.sqrt |z.1| < 1 := by
      simpa only [zero_sub, abs_neg] using (le_max_left _ _).trans_lt hp.1
    have ha : |z.1| < 1 := by
      nlinarith [Real.sq_sqrt (abs_nonneg z.1), Real.sqrt_nonneg |z.1|]
    have hx : ‖z.2‖ < 1 := by
      simpa only [zero_sub, norm_neg] using (le_max_right _ _).trans_lt hp.1
    exact ⟨(abs_lt.mp ha).1,hp.2,
      fun i => by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm z.2 i).trans_lt hx⟩
  refine ⟨h.1,?_,hs,fun z => (h.2.2.1 z).1,fun z => (h.2.2.1 z).2,h.2.2.2.1,?_⟩
  · apply (isCompact_closedBall (0 : ParabolicSpace) 1).of_isClosed_subset (isClosed_tsupport Φ)
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_le_one_of_mem_kernelPastUnitBall (hs hz)
  · intro t x
    exact h.2.2.2.2 (t,x)

end GlobalPhi43.Local
