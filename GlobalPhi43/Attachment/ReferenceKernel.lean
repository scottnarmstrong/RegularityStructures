module

public import GlobalPhi43.Attachment.ReferenceKernelMass
public import Phi43.Mollifier

/-! One concrete MW profile and the same reference mollifier. -/

public noncomputable section
namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures Set
open scoped ContDiff

/-- A fixed actual admissible profile; the mass lower bound ensures Phi0<=1. -/
@[expose] def referencePhi0 (z : ParabolicSpace) : ℝ :=
  (∫ w, referenceKernelPlateau w)⁻¹ * referenceKernelPlateau z

theorem referencePhi0_kernelProfile : MW20.KernelProfile referencePhi0 := by
  have hmass := referenceKernelPlateau_mass_ge_one
  have hpos : 0 < ∫ w, referenceKernelPlateau w := lt_of_lt_of_le (by norm_num) hmass
  have hs : tsupport referencePhi0 ⊆ referenceKernelOuter := by
    apply subset_trans _ referenceKernelPlateau_support
    apply closure_mono
    intro z hz
    exact (mul_ne_zero_iff.mp hz).2
  refine ⟨?_, isCompact_Icc.of_isClosed_subset isClosed_closure hs, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul referenceKernelPlateau_smooth
  · intro z hz
    have hh := hs hz
    refine ⟨by linarith [hh.1.1], by linarith [hh.2.1], fun i => ?_⟩
    exact abs_lt.mpr ⟨by linarith [hh.1.2 i], by linarith [hh.2.2 i]⟩
  · intro z
    exact mul_nonneg (inv_nonneg.mpr hpos.le) (referenceKernelPlateau_nonneg z)
  · intro z
    rw [referencePhi0, ← div_eq_inv_mul]
    exact (div_le_one hpos).mpr ((referenceKernelPlateau_le_one z).trans hmass)
  · change (∫ z, (∫ w, referenceKernelPlateau w)⁻¹ * referenceKernelPlateau z) = 1
    rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']
  · intro t x
    simp only [referencePhi0, referenceKernelPlateau_even]
/-- The same Phi0 supplies rho0, with no second mollifier or choice. -/
theorem referencePhi0_isMollifier : Phi43.IsMollifier referencePhi0 :=
  ⟨referencePhi0_kernelProfile.smooth, referencePhi0_kernelProfile.compact,
    referencePhi0_kernelProfile.mass⟩

end GlobalPhi43.Attachment
