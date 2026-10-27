module

public import GlobalPhi43.Compactness.Smoothing
public import GlobalPhi43.Compactness.Interpolation

@[expose] public noncomputable section

open Set Filter Topology RegularityStructures RegularityStructures.Datum
open scoped ENNReal

namespace GlobalPhi43

/-- A stronger extended-norm sublevel is exactly the closure of its continuous-function ball.
This closure identity does not require a compactness assumption. -/
theorem extNorm_sublevel_eq_closure (η : NegExponent) (α : ℝ) (M : ℝ≥0∞) :
    {z : HolderBesov η | extNorm η α z ≤ M} =
      closure (toHolderBesov η '' {f : C(Torus3, ℝ) | holderBesovENorm α f ≤ M}) := by
  apply Subset.antisymm
  · intro z hz
    apply isClosed_closure.mem_of_tendsto (tendsto_toHolderBesov_heatExt η z)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply subset_closure
    exact ⟨heatExt η z δ, (holderBesovENorm_heatExt_le_extNorm η α hδ z).trans hz, rfl⟩
  · apply closure_minimal ?_ (isClosed_extNorm_sublevel η α M)
    rintro _ ⟨f, hf, rfl⟩
    simpa only [mem_ofPred_eq, extNorm_toHolderBesov] using hf

end GlobalPhi43
