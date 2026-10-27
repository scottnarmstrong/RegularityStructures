module

public import GlobalPhi43.Invariant.Portmanteau
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Constructions.SumProd

/-! # Dense reduction for lower-semicontinuous probes -/

public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {X E Ω : Type*} [TopologicalSpace X] [TopologicalSpace E]

/-- Lower semicontinuity, rather than continuity of the probe, suffices for dense reduction. -/
theorem iSup_eq_iSup_dense {ι : Type*} (d : ι → X) (hd : DenseRange d)
    (g : X → ℝ≥0∞) (hg : LowerSemicontinuous g) :
    (⨆ x, g x) = ⨆ i, g (d i) := by
  apply le_antisymm
  · refine iSup_le fun x => hd.induction_on x (hg.isClosed_preimage _) ?_
    exact fun i => le_iSup (fun j => g (d j)) i
  · exact iSup_le fun i => le_iSup g (d i)

end GlobalPhi43.Invariant
