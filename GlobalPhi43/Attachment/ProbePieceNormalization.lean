module

public import GlobalPhi43.Attachment.ProbeCoreNormalized

/-! One family of compact unit tests represents the exact telescoping kernel
pieces, including the central piece. -/

@[expose] public noncomputable section

open RegularityStructures Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

def probePieceFactor (n : ℕ) : ℝ := (2 : ℝ)^(n+1)

def probePieceTest : ℕ → ParabolicSpace → ℝ
  | 0 => probeCoreNormalized
  | n+1 => probeAnnularNormalized (probePieceFactor (n+1))

theorem probePieceFactor_ge_two (n : ℕ) : 2 ≤ probePieceFactor n := by
  unfold probePieceFactor
  rw [pow_succ]
  nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)]

theorem probePieceTest_smooth (n : ℕ) : ContDiff ℝ ∞ (probePieceTest n) := by
  cases n with
  | zero => exact probeCoreNormalized_smooth
  | succ n => exact probeAnnularNormalized_smooth _

theorem probePieceTest_support (n : ℕ) : tsupport (probePieceTest n) ⊆
    {v | Local.pdist 0 v ≤ 1} := by
  cases n with
  | zero => exact probeCoreNormalized_support
  | succ n => exact probeAnnularNormalized_support (probePieceFactor_ge_two _)

theorem probePieceTest_compact (n : ℕ) : HasCompactSupport (probePieceTest n) :=
  (isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 1)).of_isClosed_subset
    (isClosed_tsupport _) (probePieceTest_support n)

/-- A single fixed allowance for all actual normalized pieces. -/
theorem probePieceTest_C4 : ∃ D : ℝ, 0 ≤ D ∧ ∀ n k : ℕ, k ≤ 4 → ∀ v,
    ‖iteratedFDeriv ℝ k (probePieceTest n) v‖ ≤ D*((probePieceFactor n)⁻¹)^5 := by
  obtain ⟨A, hA, ha⟩ := probeCoreNormalized_C4
  obtain ⟨B, hB, hb⟩ := probeAnnularNormalized_C4
  refine ⟨32*A+B, by positivity, ?_⟩
  intro n k hk v
  cases n with
  | zero =>
    change ‖iteratedFDeriv ℝ k probeCoreNormalized v‖ ≤ (32*A+B)*((2 : ℝ)^1)⁻¹^5
    norm_num only [pow_one, inv_pow, show (2 : ℝ)^5 = 32 by norm_num]
    linarith [ha k hk v]
  | succ n =>
    exact (hb _ (probePieceFactor_ge_two _) k hk v).trans
      (mul_le_mul_of_nonneg_right (by linarith : B ≤ 32*A+B)
        (pow_nonneg (inv_nonneg.mpr (le_trans (by norm_num) (probePieceFactor_ge_two _))) 5))

/-- Exact physical annulus, including its index and scale. -/
theorem probeGaussianPiece_succ_eq_raw {r : ℝ} (hr : 0 < r) (n : ℕ) :
    probeGaussianPiece r (n+1) = probeRawAnnulus r (probePieceFactor (n+1)) := by
  have he : 2 / (probePieceFactor (n+1)*r) = (probeDyadicRadius r (n+1))⁻¹ := by
    unfold probePieceFactor probeDyadicRadius
    rw [show n+1+1 = (n+1)+1 from rfl, pow_succ]
    field_simp
  funext z
  simp only [probeGaussianPiece, probeSpatialPiece, probeRawAnnulus, he]

/-- The literal normalized test represents the exact Gaussian piece. -/
theorem probeGaussianPiece_normalize {r : ℝ} (hr : 0 < r) (n : ℕ) (v : ParabolicSpace) :
    probeGaussianPiece r n (-parabolicDilate (probePieceFactor n*r) v) =
      ((probePieceFactor n*r)⁻¹)^5 * probePieceTest n v := by
  cases n with
  | zero => simpa only [probePieceFactor, Nat.zero_add, pow_one, probePieceTest] using
      probeGaussianPiece_core_normalize hr v
  | succ n =>
    rw [probeGaussianPiece_succ_eq_raw hr]
    exact probeRawAnnulus_normalize hr (lt_of_lt_of_le (by norm_num) (probePieceFactor_ge_two _)) v

end GlobalPhi43.Attachment
