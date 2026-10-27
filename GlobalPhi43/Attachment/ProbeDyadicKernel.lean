module

public import GlobalPhi43.Attachment.ProbeAnnularNormalized

/-! The actual scaled averaging kernel and its telescoping spatial annuli. -/

@[expose] public noncomputable section

open RegularityStructures Set Filter Topology
open scoped ContDiff

namespace GlobalPhi43.Attachment

def probeDyadicRadius (r : ℝ) (n : ℕ) : ℝ := (2 : ℝ)^n * r

theorem probeDyadicRadius_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < probeDyadicRadius r n :=
  mul_pos (pow_pos (by norm_num) _) hr

theorem probeDyadicRadius_succ (r : ℝ) (n : ℕ) :
    probeDyadicRadius r (n+1) = 2 * probeDyadicRadius r n := by
  unfold probeDyadicRadius
  rw [pow_succ]
  ring

def probeSpatialPiece (r : ℝ) : ℕ → ParabolicSpace → ℝ
  | 0, z => probeSpaceCore (r⁻¹ • z.2)
  | n+1, z => probeSpaceAnnulus ((probeDyadicRadius r (n+1))⁻¹ • z.2)

theorem probeSpatialPiece_smooth (r : ℝ) (n : ℕ) : ContDiff ℝ ∞ (probeSpatialPiece r n) := by
  cases n with
  | zero => exact probeSpaceCore_smooth.comp (by fun_prop)
  | succ n => exact probeSpaceAnnulus_smooth.comp (by fun_prop)

/-- Exact finite telescoping, with no convergence assertion substituted for identity. -/
theorem probeSpatialPiece_sum (r : ℝ) (n : ℕ) (z : ParabolicSpace) :
    (∑ j ∈ Finset.range (n+1), probeSpatialPiece r j z) =
      probeSpaceCore ((probeDyadicRadius r n)⁻¹ • z.2) := by
  induction n with
  | zero => simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, probeSpatialPiece,
      probeDyadicRadius, pow_zero, one_mul]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    change probeSpaceCore ((probeDyadicRadius r n)⁻¹ • z.2) +
      (probeSpaceCore ((probeDyadicRadius r (n+1))⁻¹ • z.2) -
        probeSpaceCore ((2 : ℝ) • ((probeDyadicRadius r (n+1))⁻¹ • z.2))) = _
    have he : (2 : ℝ) * (probeDyadicRadius r (n+1))⁻¹ = (probeDyadicRadius r n)⁻¹ := by
      rw [probeDyadicRadius_succ, mul_inv]
      ring
    rw [smul_smul, he]
    ring

/-- At every point the finite decomposition eventually equals one exactly. -/
theorem probeSpatialPiece_sum_eventually {r : ℝ} (hr : 0 < r) (z : ParabolicSpace) :
    ∀ᶠ n : ℕ in atTop, (∑ j ∈ Finset.range (n+1), probeSpatialPiece r j z) = 1 := by
  have ht : Tendsto (probeDyadicRadius r) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hr
  filter_upwards [ht.eventually_ge_atTop ‖z.2‖] with n hn
  rw [probeSpatialPiece_sum]
  apply probeSpaceCore_one
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (probeDyadicRadius_pos hr n).le),
    inv_mul_le_iff₀ (probeDyadicRadius_pos hr n), mul_one]
  exact hn

/-- The actual compact-time Gaussian probe at scale t. -/
def probeGaussianKernel (t : ℝ) (z : ParabolicSpace) : ℝ :=
  probeTimeWeight t z.1 * heatKernelR4 z

def probeGaussianPiece (r : ℝ) (n : ℕ) (z : ParabolicSpace) : ℝ :=
  probeGaussianKernel (r^2) z * probeSpatialPiece r n z

/-- Dimension five is the parabolic Jacobian: time normalization contributes
r^(-2), and the Euclidean Gaussian contributes r^(-3). -/
theorem probeGaussianKernel_dilate {r : ℝ} (hr : 0 < r) (z : ParabolicSpace) :
    probeGaussianKernel (r^2) (parabolicDilate r z) = (r⁻¹)^5 * probeGaussianProfile z := by
  have ht : (r^2 * z.1) / r^2 = z.1 := by field_simp
  change (r^2)⁻¹ * probeTimeCutoff ((r^2 * z.1) / r^2) *
    heatKernelR4 (parabolicDilate r z) = _
  rw [ht, heatKernelR4_parabolicDilate hr]
  simp only [← inv_pow]
  change (r⁻¹)^2 * probeTimeCutoff z.1 * ((r⁻¹)^3 * heatKernelR4 z) =
    (r⁻¹)^5 * (probeTimeCutoff z.1 * heatKernelR4 z)
  rw [show (5 : ℕ) = 2+3 from rfl, pow_add]
  ring

/-- The actual finite kernel sum and its eventual pointwise identification. -/
theorem probeGaussianPiece_sum (r : ℝ) (n : ℕ) (z : ParabolicSpace) :
    (∑ j ∈ Finset.range (n+1), probeGaussianPiece r j z) =
      probeGaussianKernel (r^2) z * probeSpaceCore ((probeDyadicRadius r n)⁻¹ • z.2) := by
  simp only [probeGaussianPiece, ← Finset.mul_sum, probeSpatialPiece_sum]

end GlobalPhi43.Attachment
