module

public import GlobalPhi43.Attachment.ProbePieceNormalization
public import GlobalPhi43.Attachment.ProbeKernelIntegral
public import GlobalPhi43.Attachment.ProbeCompactPairing

/-! Smoothness, support, and exact physical pullback for every Gaussian piece. -/

@[expose] public noncomputable section

open RegularityStructures Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

theorem probeGaussianPiece_smooth {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ ∞ (probeGaussianPiece r n) :=
  (probeGaussianKernel_smooth hr).mul (probeSpatialPiece_smooth r n)

theorem probeGaussianPiece_time_support {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) :
    tsupport (probeGaussianPiece r n) ⊆ {z | z.1 ∈ Icc (0 : ℝ) 1} := by
  intro z hz
  have hk : z ∈ tsupport (probeGaussianKernel (r^2)) := tsupport_mul_subset_left hz
  have ht := probeGaussianKernel_time_support (sq_pos_of_pos hr) hk
  change 0 ≤ z.1 ∧ z.1 ≤ 1
  constructor <;> nlinarith [ht.1, ht.2]

theorem probeGaussianPiece_space_support {r : ℝ} (hr : 0 < r) (n : ℕ)
    (z : ParabolicSpace) (hz : probeGaussianPiece r n z ≠ 0) :
    ‖z.2‖ ≤ (2 : ℝ)^(n+1)*r := by
  have hs : probeSpatialPiece r n z ≠ 0 := by
    intro he
    exact hz (by simp only [probeGaussianPiece, he, mul_zero])
  cases n with
  | zero =>
    have hh := probeSpaceCore_support (subset_closure hs)
    change ‖r⁻¹ • z.2-0‖ ≤ 2 at hh
    rw [sub_zero, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_le_iff₀ hr] at hh
    simpa only [Nat.zero_add, pow_one, mul_comm] using hh
  | succ n =>
    have hh := (probeSpaceAnnulus_support (subset_closure hs)).2
    have hp := probeDyadicRadius_pos hr (n+1)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_le_iff₀ hp] at hh
    exact hh.trans_eq (by unfold probeDyadicRadius; rw [pow_succ]; ring)

theorem probeGaussianPiece_formula {r : ℝ} (hr : 0 < r) (n : ℕ) (z : ParabolicSpace) :
    probeGaussianPiece r n z = ((probePieceFactor n*r)⁻¹)^5 *
      probePieceTest n (probeNegativeDilate ((probePieceFactor n*r)⁻¹) z) := by
  have hp : probePieceFactor n*r ≠ 0 :=
    (mul_pos (lt_of_lt_of_le (by norm_num) (probePieceFactor_ge_two _)) hr).ne'
  have he : -parabolicDilate (probePieceFactor n*r)
      (probeNegativeDilate ((probePieceFactor n*r)⁻¹) z) = z := by
    change -(parabolicDilateCLM _ (-parabolicDilateCLM _ z)) = z
    rw [map_neg, neg_neg, parabolicDilateCLM_apply, parabolicDilateCLM_apply,
      parabolicDilate_parabolicDilate_inv hp]
  have hh := probeGaussianPiece_normalize hr n (probeNegativeDilate ((probePieceFactor n*r)⁻¹) z)
  rwa [he] at hh

/-- The pairing is with the literal rescaled unit test at the original base. -/
theorem probeGaussianPiece_rescaled {r : ℝ} (hr : 0 < r) (n : ℕ) (z w : ParabolicSpace) :
    probeGaussianPiece r n (z-w) =
      rescaledTestFunction (probePieceTest n) (probePieceFactor n*r) z w := by
  rw [probeGaussianPiece_formula hr]
  have he : probeNegativeDilate ((probePieceFactor n*r)⁻¹) (z-w) =
      parabolicDilate ((probePieceFactor n*r)⁻¹) (w-z) := by
    change -(parabolicDilateCLM _ (z-w)) = _
    rw [map_sub, neg_sub, parabolicDilateCLM_apply, parabolicDilateCLM_apply,
      ← parabolicDilate_sub]
  rw [he]
  simp only [rescaledTestFunction, inv_pow]

end GlobalPhi43.Attachment
