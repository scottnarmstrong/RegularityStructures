module

public import GlobalPhi43.Attachment.ProbeKernelNormalization

/-! The central Gaussian piece is one fixed compact unit test, with a genuine
finite C4 allowance obtained from the constructed profile. -/

@[expose] public noncomputable section

open RegularityStructures Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

def probeCoreNormalized (v : ParabolicSpace) : ℝ :=
  (2 : ℝ)^5 * probeGaussianProfile (probeNegativeDilate 2 v) * probeSpaceCore ((-2 : ℝ) • v.2)

theorem probeCoreNormalized_smooth : ContDiff ℝ ∞ probeCoreNormalized := by
  unfold probeCoreNormalized
  exact (contDiff_const.mul (probeGaussianProfile_smooth.comp (probeNegativeDilate 2).contDiff)).mul
    (probeSpaceCore_smooth.comp (by fun_prop))

theorem probeCoreNormalized_support : tsupport probeCoreNormalized ⊆
    {v | Local.pdist 0 v ≤ 1} := by
  apply closure_minimal _ (isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 1)).isClosed
  intro v hv
  have hg : probeGaussianProfile (probeNegativeDilate 2 v) ≠ 0 := by
    intro he
    exact hv (by simp only [probeCoreNormalized, he, mul_zero, zero_mul])
  have hs : probeSpaceCore ((-2 : ℝ) • v.2) ≠ 0 := by
    intro he
    exact hv (by simp only [probeCoreNormalized, he, mul_zero])
  have hx := probeSpaceCore_support (subset_closure hs)
  have hx' : ‖v.2‖ ≤ 1 := by
    change ‖(-2 : ℝ) • v.2 - 0‖ ≤ 2 at hx
    rw [sub_zero, norm_smul, Real.norm_eq_abs] at hx
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hx
    linarith
  have ht := probeGaussianProfile_support (subset_closure hg)
  change 1/2 ≤ -((2 : ℝ)^2*v.1) ∧ -((2 : ℝ)^2*v.1) ≤ 3/4 at ht
  have ht' : |v.1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  change max (Real.sqrt |0-v.1|) ‖0-v.2‖ ≤ 1
  simp only [zero_sub, abs_neg, norm_neg]
  exact max_le ((Real.sqrt_le_left zero_le_one).mpr (by simpa only [one_pow] using ht')) hx'

theorem probeCoreNormalized_compact : HasCompactSupport probeCoreNormalized :=
  (isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 1)).of_isClosed_subset
    (isClosed_tsupport _) probeCoreNormalized_support

theorem probeCoreNormalized_C4 : ∃ A : ℝ, 0 ≤ A ∧ ∀ k ≤ 4, ∀ z,
    ‖iteratedFDeriv ℝ k probeCoreNormalized z‖ ≤ A :=
  probeCoreNormalized_compact.exists_bound_iteratedFDeriv probeCoreNormalized_smooth 4

theorem probeGaussianPiece_core_normalize {r : ℝ} (hr : 0 < r) (v : ParabolicSpace) :
    probeGaussianPiece r 0 (-parabolicDilate (2*r) v) =
      ((2*r)⁻¹)^5 * probeCoreNormalized v := by
  have he : -parabolicDilate (2*r) v = parabolicDilate r (probeNegativeDilate 2 v) := by
    ext i <;> simp [parabolicDilate, probeNegativeDilate] <;> ring
  have hs : r⁻¹ • (-parabolicDilate (2*r) v).2 = (-2 : ℝ) • v.2 := by
    ext i
    simp only [parabolicDilate, Prod.snd_neg, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    field_simp
  change probeGaussianKernel (r^2) (-parabolicDilate (2*r) v) *
    probeSpaceCore (r⁻¹ • (-parabolicDilate (2*r) v).2) = _
  rw [hs, he, probeGaussianKernel_dilate hr]
  unfold probeCoreNormalized
  have hn : ((2*r)⁻¹)^5 * (2 : ℝ)^5 = (r⁻¹)^5 := by
    rw [mul_inv, mul_pow]
    ring
  calc _ = (((2*r)⁻¹)^5 * (2 : ℝ)^5) * probeGaussianProfile (probeNegativeDilate 2 v) *
      probeSpaceCore ((-2 : ℝ) • v.2) := by rw [hn]
    _ = _ := by ring

end GlobalPhi43.Attachment
