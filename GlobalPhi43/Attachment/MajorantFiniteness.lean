module

public import GlobalPhi43.Attachment.MajorantRegions
public import GlobalPhi43.Attachment.AttachmentFunctionalBound
public import GlobalPhi43.Attachment.MassiveRegularity
public import GlobalPhi43.Flow.MajorantLaterState

/-! Finiteness of the deterministic physical majorant windows.
No solution bound, bounded-defect estimate or slice estimate is assumed. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local
open scoped ENNReal Pointwise

namespace GlobalPhi43.Attachment

/-- The Minkowski region equals the closed radius-four enlargement. -/
theorem majorantRegion_eq_radiusFour (s : ℝ) :
    Flow.majorantRegion s = radiusFourRegion (Flow.coverRegion s ∪ Flow.sliceRegion s) := by
  ext y
  constructor
  · rintro ⟨z, hz, w, hw, rfl⟩
    refine ⟨z, hz, ?_⟩
    have he : pdist z (z+w) = pdist 0 w := by simp [pdist]
    rw [he]
    exact hw
  · intro hy
    exact radiusFourRegion_subset_majorant (s := s) (fun _ h => h) hy

theorem isCompact_majorantRegion (s : ℝ) : IsCompact (Flow.majorantRegion s) := by
  rw [majorantRegion_eq_radiusFour]
  exact isCompact_parabolic_enlargement
    ((isCompact_coverRegion s).union (isCompact_sliceRegion s)) (by norm_num : (0:ℝ) ≤ 4)

end GlobalPhi43.Attachment
