module

public import GlobalPhi43.Attachment.AttachmentFunctionalBound
public import GlobalPhi43.Attachment.MajorantRegions
public import GlobalPhi43.Flow.LocalConsistency

/-! The tree functional on the cover window. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

/-- One coefficient works for all lift data and starting times in the
functional estimate used by the Moinat–Weber bound. -/
theorem cover_functional_bound (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ∃ K : ℝ≥0, ∀ (a : Flow.LiftData N κ) (s : ℝ),
      attachmentFunctional N κ Φ hΦ a.forcing a.constants (Flow.coverRegion s) ≤
        (K : ℝ≥0∞) * (1 + a.model.normOn (gamma κ) (Flow.majorantRegion s))^7 := by
  obtain ⟨c, hc, h⟩ := attachment_functional_bound N κ Φ hΦ
  refine ⟨c.toNNReal, ?_⟩
  intro a s
  have hb := h a.forcing a.constants a.model (Flow.smooth_of_moderateLift a.moderate)
    a.moderate.1 a.moderate.2.1 (Flow.coverRegion s) (isCompact_coverRegion s)
  have hm : a.model.normOn (gamma κ) (radiusFourRegion (Flow.coverRegion s)) ≤
      a.model.normOn (gamma κ) (Flow.majorantRegion s) :=
    attachment_normOn_mono a.model (coverRadiusFour_subset_majorant s)
  apply hb.trans
  change ENNReal.ofReal (c * (1 +
    (a.model.normOn (gamma κ) (radiusFourRegion (Flow.coverRegion s))).toReal) ^ (7 : ℝ)) ≤
      ENNReal.ofReal c * (1 + a.model.normOn (gamma κ) (Flow.majorantRegion s))^7
  simp only [Real.rpow_ofNat]
  rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1) ENNReal.toReal_nonneg,
    ENNReal.ofReal_one]
  have hn : ENNReal.ofReal
      (a.model.normOn (gamma κ) (radiusFourRegion (Flow.coverRegion s))).toReal ≤
      a.model.normOn (gamma κ) (Flow.majorantRegion s) :=
    ENNReal.ofReal_toReal_le.trans hm
  gcongr

end GlobalPhi43.Attachment
