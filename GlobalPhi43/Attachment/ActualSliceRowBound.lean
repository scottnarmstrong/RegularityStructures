module

public import GlobalPhi43.Attachment.SliceRadiusFour
public import GlobalPhi43.Attachment.ConditionalEveryStart

@[expose] public noncomputable section
namespace GlobalPhi43.Attachment
open Set RegularityStructures RegularityStructures.Phi43
open scoped NNReal

/-- The radius-four slice bound at the same regularity exponent.
The slice, PDE, defect and integrability estimates follow from the deterministic bounds. -/
theorem exists_actualSliceRow (N : ℕ) (κ : Kappa) :
    ∃ H : ℝ≥0, ActualSliceRow N κ H := by
  obtain ⟨c,_hc,h⟩ := slice_radius_four N κ
  refine ⟨c.toNNReal,?_⟩
  intro a s _hs t ht
  have hb := h a.forcing a.constants a.model (Flow.smooth_of_moderateLift a.moderate)
    a.moderate.1 a.moderate.2.1 a.potential a.moderate.2.2 s t ht
  have hm := attachment_normOn_mono a.model (sliceRadiusFour_subset_majorant s)
  apply hb.trans
  change ENNReal.ofReal c * _ ≤ ENNReal.ofReal c * _
  gcongr

end GlobalPhi43.Attachment
