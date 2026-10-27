module

public import GlobalPhi43.Attachment.ProbeKernelNormalization
public import GlobalPhi43.Attachment.ProbeFoldBounds

/-! At physical scales at least one, the normalized annular test pulls back
by a contraction. Thus its proved C4 allowance also controls the folded tests. -/

@[expose] public noncomputable section

open RegularityStructures
open scoped ContDiff

namespace GlobalPhi43.Attachment

theorem probeNegativeDilate_norm_small {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ 1) :
    ‖probeNegativeDilate a‖ ≤ 1 := by
  apply (probeNegativeDilate a).opNorm_le_bound zero_le_one
  intro z
  change ‖-parabolicDilate a z‖ ≤ 1*‖z‖
  rw [norm_neg, one_mul, parabolicDilate, Prod.norm_def]
  apply max_le
  · rw [norm_mul, Real.norm_of_nonneg (sq_nonneg a)]
    exact (mul_le_of_le_one_left (norm_nonneg z.1) (by nlinarith : a^2 ≤ 1)).trans (norm_fst_le z)
  · rw [norm_smul, Real.norm_of_nonneg ha]
    exact (mul_le_of_le_one_left (norm_nonneg z.2) hb).trans (norm_snd_le z)
end GlobalPhi43.Attachment
