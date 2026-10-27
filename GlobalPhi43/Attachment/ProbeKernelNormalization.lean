module

public import GlobalPhi43.Attachment.ProbeDyadicKernel

/-! Exact identification of the constructed tests with the physical Gaussian
pieces. No test estimate is assumed in these change-of-scale identities. -/

@[expose] public noncomputable section

open RegularityStructures Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

theorem probeGaussianKernel_formula {r : ℝ} (hr : 0 < r) (z : ParabolicSpace) :
    probeGaussianKernel (r^2) z =
      (r⁻¹)^5 * probeGaussianProfile (parabolicDilate r⁻¹ z) := by
  have hh := probeGaussianKernel_dilate hr (parabolicDilate r⁻¹ z)
  rwa [parabolicDilate_parabolicDilate_inv hr.ne'] at hh

theorem probeGaussianKernel_smooth {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (probeGaussianKernel (r^2)) := by
  have he : probeGaussianKernel (r^2) = fun z =>
      (r⁻¹)^5 * probeGaussianProfile (parabolicDilateCLM r⁻¹ z) := by
    funext z
    simpa only [parabolicDilateCLM_apply] using probeGaussianKernel_formula hr z
  rw [he]
  exact contDiff_const.mul (probeGaussianProfile_smooth.comp (parabolicDilateCLM _).contDiff)

/-- The generic physical annulus; c is twice its radius in units of r. -/
def probeRawAnnulus (r c : ℝ) (z : ParabolicSpace) : ℝ :=
  probeGaussianKernel (r^2) z * probeSpaceAnnulus ((2 / (c*r)) • z.2)

theorem probeRawAnnulus_normalize {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (v : ParabolicSpace) :
    probeRawAnnulus r c (-parabolicDilate (c*r) v) =
      ((c*r)⁻¹)^5 * probeAnnularNormalized c v := by
  have he : -parabolicDilate (c*r) v =
      parabolicDilate r (probeNegativeDilate c v) := by
    ext i <;> simp [parabolicDilate, probeNegativeDilate] <;> ring
  have hs : (2 / (c*r)) • (-parabolicDilate (c*r) v).2 = (-2 : ℝ) • v.2 := by
    ext i
    simp only [parabolicDilate, Prod.snd_neg, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    field_simp
  unfold probeRawAnnulus
  rw [hs, he, probeGaussianKernel_dilate hr]
  unfold probeAnnularNormalized probeAnnularSpatialLift
  have hn : ((c*r)⁻¹)^5 * c^5 = (r⁻¹)^5 := by
    rw [mul_inv, mul_pow, mul_assoc, ← mul_pow]
    field_simp
  calc _ = (((c*r)⁻¹)^5*c^5) * probeGaussianProfile (probeNegativeDilate c v) *
      probeSpaceAnnulus ((-2 : ℝ) • v.2) := by rw [hn]
    _ = _ := by ring

end GlobalPhi43.Attachment
