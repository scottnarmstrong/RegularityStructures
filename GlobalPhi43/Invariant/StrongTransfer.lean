module

public import GlobalPhi43.Invariant.DenseSup
public import GlobalPhi43.Invariant.LateMoments
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Semicontinuity.Basic

/-! # Real powers of extended suprema -/

public noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {E X Ω : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [MeasurableSpace Ω]

/-- Real powers of the extended supremum commute with the supremum, for p>0. -/
theorem iSup_rpow_eq {ι : Type*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p :=
  Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
    (fun _ _ h => ENNReal.rpow_le_rpow h hp.le) (ENNReal.zero_rpow_of_pos hp)

end GlobalPhi43.Invariant
